/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C057C001Part025`. -/


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
noncomputable def nb057_split_alpha_0065 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
        ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
        ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
        ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
        ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_144))
            (syn_cun (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_147 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_148 f))
              (Class.cv (nb057_alpha_dummy_149 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
          ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
          ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
          ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
          ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
          ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
          ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0066 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
        (syn_cphi (Class.cv (nb057_alpha_dummy_131))))
      (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
        (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
            ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0136) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0137 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0136) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0137 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0134) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
                                      ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
                                      ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
                                      ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                                      ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
                                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                                      ((nb057_alpha_dummy_000), a),
                                      ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
                                        (nb057_alpha_dummy_003 f a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057_split_alpha_0065 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                          ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                          ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                          ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
                          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                          ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                          ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                          ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
                          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0067 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
        ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
        ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
        ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
        ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
        ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_144))
            (syn_cun (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_147 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_148 f))
              (Class.cv (nb057_alpha_dummy_149 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
          ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
          ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
          ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
          ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
          ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
          ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
          ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
          ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0068 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
        ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_138))
          (Class.cv (nb057_alpha_dummy_131))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_139))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_138))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f))
          (Class.cv (nb057_alpha_dummy_133 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_141 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_140 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0162) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0163 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0160) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0161 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0136) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0137 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
                                  ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
                                  ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
                                  ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                                  ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                                  ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                                  ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
                                  ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                                  ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                                  ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                                  ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                                  ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                                  ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                  ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                  ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                  ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                                  ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0067 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                      ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
                      ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                      ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                      ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
                      ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                      ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0069 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_160))
          (Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_160))
            (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_161 f))
          (Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_161 f))
            (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0158) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0159 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0155) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0157 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0068 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0068 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                          ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0158) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0159 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0155) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0157 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057_alpha_dummy_124))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0068 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0068 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                            ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                            ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                            ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                            ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                            ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                            ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                            ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                            ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                            ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part026`. -/


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
noncomputable def nb057_split_alpha_0070 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
        ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
        ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
        ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
        ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_180))
            (syn_cun (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_183 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_184 f))
              (Class.cv (nb057_alpha_dummy_185 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
          ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
          ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
          ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
          ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
          ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
          ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0071 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
        (syn_cphi (Class.cv (nb057_alpha_dummy_167))))
      (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
        (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
            ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_167))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_169 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0174) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0175 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0174) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0175 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0172) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
                                      ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
                                      ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
                                      ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                                      ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
                                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                                      ((nb057_alpha_dummy_000), a),
                                      ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
                                        (nb057_alpha_dummy_003 f a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057_split_alpha_0070 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                          ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                          ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                          ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
                          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                          ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                          ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                          ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
                          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0072 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
        ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
        ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
        ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
        ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
        ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_180))
            (syn_cun (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_183 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_184 f))
              (Class.cv (nb057_alpha_dummy_185 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
          ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
          ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
          ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
          ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
          ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
          ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
          ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
          ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0073 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
        ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_174))
          (Class.cv (nb057_alpha_dummy_167))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_175))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_174))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_176 f))
          (Class.cv (nb057_alpha_dummy_169 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_177 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_176 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0200) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0201 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0198) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0199 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_167))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_169 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0174) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0175 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0174) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0175 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0172) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
                                  ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
                                  ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
                                  ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                                  ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                                  ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                                  ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
                                  ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                                  ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                                  ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                                  ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                                  ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                                  ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                  ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                  ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                  ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                                  ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0072 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                      ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
                      ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                      ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                      ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
                      ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                      ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part027`. -/


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
noncomputable def nb057_split_alpha_0074 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_196))
          (Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_196))
            (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_197 f))
          (Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_197 f))
            (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0196) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0197 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0193) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0195 f) 0))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0073 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0073 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                          ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0196) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0197 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0193) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057_alpha_dummy_125))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0073 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0073 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                            ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                            ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                            ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                            ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                            ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                            ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                            ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                            ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                            ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb057_final_composition_variable_occurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Class.cv (nb057_alpha_dummy_001)) (Class.cv f) :=
  by
  have freshness0 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_125) :=
    by
    unfold nb057_alpha_dummy_125
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 1))
  have freshness1 : f ≠ (nb057_alpha_dummy_127 f) :=
    by
    unfold nb057_alpha_dummy_127
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 1))
  have freshness2 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_124) :=
    by
    unfold nb057_alpha_dummy_124
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 0))
  have freshness3 : f ≠ (nb057_alpha_dummy_126 f) :=
    by
    unfold nb057_alpha_dummy_126
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 0))
  have freshness4 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_128) :=
    by
    unfold nb057_alpha_dummy_128
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0210) 0))
  have freshness5 : f ≠ (nb057_alpha_dummy_129 f) :=
    by
    unfold nb057_alpha_dummy_129
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0211 f) 0))
  have freshness6 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_239) :=
    by
    unfold nb057_alpha_dummy_239
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0290) 1))
  have freshness7 : f ≠ (nb057_alpha_dummy_241 f) :=
    by
    unfold nb057_alpha_dummy_241
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0291 f) 1))
  have freshness8 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_238) :=
    by
    unfold nb057_alpha_dummy_238
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0290) 0))
  have freshness9 : f ≠ (nb057_alpha_dummy_240 f) :=
    by
    unfold nb057_alpha_dummy_240
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0291 f) 0))
  have freshness10 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_000) :=
    by
    unfold nb057_alpha_dummy_001 nb057_alpha_dummy_000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness11 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11 (TAlphaVar.here _ _ _))))))))

@[expose]
noncomputable def nb057_split_alpha_0075 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq (Class.cv (nb057_alpha_dummy_128))
          (syn_cop (Class.cv (nb057_alpha_dummy_124)) (Class.cv (nb057_alpha_dummy_125))))
        (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))))
      (Wff.imp (Wff.classEq (Class.cv (nb057_alpha_dummy_129 f))
          (syn_cop (Class.cv (nb057_alpha_dummy_126 f)) (Class.cv (nb057_alpha_dummy_127 f))))
        (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0124) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0125 f) 0)))
          (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0122) 0)))
            (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0123 f) 0)))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0126) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0126) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0130) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0131 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0127) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (nb057_split_alpha_0066 f a)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0126) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0126) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0130) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0131 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0127) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (nb057_split_alpha_0066 f a)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0069 f a)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0164) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0164) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0168) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0165) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb057_split_alpha_0071 f a)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0164) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0164) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0168) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0165) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb057_split_alpha_0071 f a)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0074 f a))))))))
        (nb057_final_composition_variable_occurrence f a dv_a_f))))

@[expose]
noncomputable def nb057_final_pair_binder_occurrence (f : Var) (a : Var) :
    TAlphaClass
      [((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Class.cv (nb057_alpha_dummy_050)) (Class.cv (nb057_alpha_dummy_051 f)) :=
  by
  have freshness0 : (nb057_alpha_dummy_050) ≠ (nb057_alpha_dummy_045) :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0044) 0)))
  have freshness1 : (nb057_alpha_dummy_051 f) ≠ (nb057_alpha_dummy_048 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0045 f) 0)))
  have freshness2 : (nb057_alpha_dummy_050) ≠ (nb057_alpha_dummy_044) :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0042) 0)))
  have freshness3 : (nb057_alpha_dummy_051 f) ≠ (nb057_alpha_dummy_047 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0043 f) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb057_split_alpha_0076 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (syn_wfun (Class.cv (nb057_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb057_alpha_dummy_001)))
            (Class.cv (nb057_alpha_dummy_000)))))
      (Wff.imp (syn_wfun (Class.cv f))
        (Wff.neg (Wff.classEq (syn_cdm (Class.cv f)) (Class.cv a)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0032 f a dv_a_f)))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classEq (nb057_final_pair_binder_occurrence f a) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0049 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb057_split_alpha_0034 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0049 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb057_split_alpha_0034 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb057_split_alpha_0037 f a)))))))))
              (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0059 f a dv_a_f))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                    ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                    ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                    ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0061 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0061 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb057_split_alpha_0064 f a)))))))) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex
                      (TAlphaWff.neg (nb057_split_alpha_0075 f a dv_a_f)))))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _)))))

@[expose]
noncomputable def nominal_df_fns (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    Nominal.NPrf (.classEq (syn_cfns) (syn_copab f a (syn_wfn (.cv f) (.cv a)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb057_split_alpha_0004 f a dv_a_f)
              (TAlphaWff.neg (nb057_split_alpha_0076 f a dv_a_f))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
