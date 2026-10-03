/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C056C001Block002

/-! NF weak partition development: NAR4C056C001Part013. -/


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
noncomputable def nb056_split_alpha_0023 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)),
        ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)),
        ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)),
        ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
        ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
        ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
        ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)),
        ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
        ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
        ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
        ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
        ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_177))
            (syn_cun (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_180 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_181 f))
              (Class.cv (nb056_alpha_dummy_182 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)),
          ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)),
          ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)),
          ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
          ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
          ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
          ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)),
          ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
          ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
          ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
          ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
          ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0024 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
        ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
        ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)),
        ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
        ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
        ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
        ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
        ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_171))
          (Class.cv (nb056_alpha_dummy_164))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_172))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_171))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_173 f))
          (Class.cv (nb056_alpha_dummy_166 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_174 f))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_173 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0208) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0209 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0206) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0207 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_164))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_166 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0182) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0183 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0182) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0183 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)),
                                  ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)),
                                  ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)),
                                  ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
                                  ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
                                  ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
                                  ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)),
                                  ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
                                  ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                                  ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                                  ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
                                  ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                  ((nb056_alpha_dummy_000), f)]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056_split_alpha_0023 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
                      ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
                      ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
                      ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)),
                      ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
                      ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                      ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                      ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
                      ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
                      ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
                      ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
                      ((nb056_alpha_dummy_197), (nb056_alpha_dummy_198 f)),
                      ((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
                      ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                      ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                      ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
                      ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb056_split_alpha_0025 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
        ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_193))
          (Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_193))
            (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_194 f))
          (Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056_alpha_dummy_194 f))
            (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0204) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0205 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0201) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0203 f) 0))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb056_alpha_dummy_000))).fv ∪
                              ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb056_alpha_dummy_007))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0024 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0024 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
                          ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                          ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                          ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
                          ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0204) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0205 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0201) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0203 f) 0))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb056_alpha_dummy_000))).fv ∪
                                ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056_alpha_dummy_007))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0024 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0024 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb056_alpha_dummy_195), (nb056_alpha_dummy_196 f)),
                            ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                            ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                            ((nb056_alpha_dummy_193), (nb056_alpha_dummy_194 f)),
                            ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                            ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                            ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                            ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                            ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                            ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                            ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                            ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb056_compose_variable_occurrence (f : Var) :
    TAlphaClass
      [(nb056_alpha_dummy_007, (nb056_alpha_dummy_010 f)),
        (nb056_alpha_dummy_006, (nb056_alpha_dummy_009 f)),
        (nb056_alpha_dummy_005, (nb056_alpha_dummy_008 f)),
        (nb056_alpha_dummy_011, (nb056_alpha_dummy_012 f)),
        (nb056_alpha_dummy_003, (nb056_alpha_dummy_004 f)),
        (nb056_alpha_dummy_001, (nb056_alpha_dummy_002 f)), (nb056_alpha_dummy_000, f)]
      (Class.cv nb056_alpha_dummy_000) (Class.cv f) :=
  by
  have freshness0 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_007 :=
    by
    unfold nb056_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  have freshness1 : f ≠ (nb056_alpha_dummy_010 f) :=
    by
    unfold nb056_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  have freshness2 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_006 :=
    by
    unfold nb056_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 1))
  have freshness3 : f ≠ (nb056_alpha_dummy_009 f) :=
    by
    unfold nb056_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 1))
  have freshness4 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_005 :=
    by
    unfold nb056_alpha_dummy_005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 0))
  have freshness5 : f ≠ (nb056_alpha_dummy_008 f) :=
    by
    unfold nb056_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 0))
  have freshness6 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_011 :=
    by
    unfold nb056_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0165) 0))
  have freshness7 : f ≠ (nb056_alpha_dummy_012 f) :=
    by
    unfold nb056_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0167 f) 0))
  have freshness8 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_003 :=
    by
    unfold nb056_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0162) 0))
  have freshness9 : f ≠ (nb056_alpha_dummy_004 f) :=
    by
    unfold nb056_alpha_dummy_004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0163 f) 0))
  have freshness10 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_001 :=
    by
    unfold nb056_alpha_dummy_001
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0160) 0))
  have freshness11 : f ≠ (nb056_alpha_dummy_002 f) :=
    by
    unfold nb056_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0161 f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11 (TAlphaVar.here _ _ _))))))))

@[expose]
noncomputable def nb056_split_alpha_0026 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (syn_wbr (Class.cv (nb056_alpha_dummy_005))
          (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007)))
        (Wff.neg (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_006)))))
      (Wff.imp (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb056_alpha_dummy_010 f))) (Wff.neg
          (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_009 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0042) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0042) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0046) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0047 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0043) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0045 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb056_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb056_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb056_split_alpha_0006 f)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0042) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0042) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0046) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0047 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0043) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0045 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv
        (Class.cv (nb056_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv
        (nb056_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb056_split_alpha_0006 f)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0009 f)))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb056_split_alpha_0020 f))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0172) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0172) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0176) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0177 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0173) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0175 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb056_split_alpha_0022 f)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0172) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0172) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0176) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0177 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0173) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0175 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb056_split_alpha_0022 f)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0025 f))))))))
        (nb056_compose_variable_occurrence f))))

theorem nb056_wpp_notmem_0490 : (nb056_alpha_dummy_003) ∉ ((syn_cid)).fv := by
  simpa only [nb056_alpha_dummy_003, fv_syn_cid] using (nb056_compact_fv_empty_0026)

theorem nb056_wpp_notmem_0491 (f : Var) : (nb056_alpha_dummy_004 f) ∉ ((syn_cid)).fv := by
  simpa only [nb056_alpha_dummy_004, fv_syn_cid] using (nb056_compact_fv_empty_0027 f)

theorem nb056_wpp_notmem_0492 : (nb056_alpha_dummy_001) ∉ ((syn_cid)).fv := by
  simpa only [nb056_alpha_dummy_001, fv_syn_cid] using (nb056_compact_fv_empty_0028)

theorem nb056_wpp_notmem_0493 (f : Var) : (nb056_alpha_dummy_002 f) ∉ ((syn_cid)).fv := by
  simpa only [nb056_alpha_dummy_002, fv_syn_cid] using (nb056_compact_fv_empty_0029 f)

theorem nb056_wpp_notmem_0494 : (nb056_alpha_dummy_000) ∉ ((syn_cid)).fv := by
  simpa only [nb056_alpha_dummy_000, fv_syn_cid] using (nb056_compact_fv_empty_0030)

theorem nb056_wpp_notmem_0495 (f : Var) : f ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb056_compact_fv_empty_0031 f)

theorem nb056_compact_envfresh_0035 (f : Var) :
    TEnvFresh
      [((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb056_alpha_dummy_003) (nb056_alpha_dummy_004 f)
      (nb056_wpp_notmem_0490) (nb056_wpp_notmem_0491 f)
      (TEnvFresh.consFresh (nb056_alpha_dummy_001) (nb056_alpha_dummy_002 f)
        (nb056_wpp_notmem_0492) (nb056_wpp_notmem_0493 f)
        (TEnvFresh.consFresh (nb056_alpha_dummy_000) f (nb056_wpp_notmem_0494)
          (nb056_wpp_notmem_0495 f) (TEnvFresh.nil ((syn_cid)).fv))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
