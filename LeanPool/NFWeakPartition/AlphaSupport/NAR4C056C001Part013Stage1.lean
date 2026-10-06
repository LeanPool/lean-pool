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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0023`. -/
@[expose]
noncomputable def nb056SplitAlpha0023 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
        ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
        ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
        ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
        ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
        ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
        ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
        ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
        ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
        ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
        ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy177))
            (synCun (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy180 f))
            (synCun (Class.cv (nb056AlphaDummy181 f))
              (Class.cv (nb056AlphaDummy182 f)))))) :=
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
                                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
          ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
          ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
          ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
          ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
          ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
          ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
          ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
          ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
          ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
          ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
          ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
          ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
          ((nb056AlphaDummy001), (nb056AlphaDummy002 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (by decide))
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
                                  (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0024`. -/
@[expose]
noncomputable def nb056SplitAlpha0024 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
        ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
        ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
        ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
        ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
        ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
        ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy171))
          (Class.cv (nb056AlphaDummy164))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy172))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy171)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy171)) (synC1c))
              (Class.cv (nb056AlphaDummy171))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy173 f))
          (Class.cv (nb056AlphaDummy166 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy174 f))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy173 f)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy173 f)) (synC1c))
              (Class.cv (nb056AlphaDummy173 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb056AlphaDummy164))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy166 f))).fv) (by decide))
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
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
                                  ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
                                  ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
                                  ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                                  ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                                  ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                                  ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
                                  ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                                  ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                                  ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                                  ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                                  ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                                  ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0023 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                      ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                      ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                      ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
                      ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                      ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                      ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                      ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                      ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                      ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                      ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                      ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                      ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
                      ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                      ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                      ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                      ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                      ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                      ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0025`. -/
@[expose]
noncomputable def nb056SplitAlpha0025 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
        ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy193))
          (Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056AlphaDummy193))
            (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy194 f))
          (Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy194 f))
            (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                    (synCsn (synC0c))))))))) :=
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
                            (((Class.cv (nb056AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb056AlphaDummy007))).fv ∪
                      ((Class.cv (nb056AlphaDummy006))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056AlphaDummy010 f))).fv ∪
                      ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0024 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0024 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                          ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                          ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                          ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                          ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                          ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                          ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                          ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c)))
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
                              (((Class.cv (nb056AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056AlphaDummy007))).fv ∪
                        ((Class.cv (nb056AlphaDummy006))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy010 f))).fv ∪
                        ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0024 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0024 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                            ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                            ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                            ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                            ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                            ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                            ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                            ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                            ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                            ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                            ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                            ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as
`nb056_compose_variable_occurrence`.
-/
@[expose]
noncomputable def nb056ComposeVariableOccurrence (f : Var) :
    TAlphaClass
      [(nb056AlphaDummy007, (nb056AlphaDummy010 f)),
        (nb056AlphaDummy006, (nb056AlphaDummy009 f)),
        (nb056AlphaDummy005, (nb056AlphaDummy008 f)),
        (nb056AlphaDummy011, (nb056AlphaDummy012 f)),
        (nb056AlphaDummy003, (nb056AlphaDummy004 f)),
        (nb056AlphaDummy001, (nb056AlphaDummy002 f)), (nb056AlphaDummy000, f)]
      (Class.cv nb056AlphaDummy000) (Class.cv f) :=
  by
  have freshness0 : nb056AlphaDummy000 ≠ nb056AlphaDummy007 :=
    by
    unfold nb056AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  have freshness1 : f ≠ (nb056AlphaDummy010 f) :=
    by
    unfold nb056AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  have freshness2 : nb056AlphaDummy000 ≠ nb056AlphaDummy006 :=
    by
    unfold nb056AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 1))
  have freshness3 : f ≠ (nb056AlphaDummy009 f) :=
    by
    unfold nb056AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 1))
  have freshness4 : nb056AlphaDummy000 ≠ nb056AlphaDummy005 :=
    by
    unfold nb056AlphaDummy005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 0))
  have freshness5 : f ≠ (nb056AlphaDummy008 f) :=
    by
    unfold nb056AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 0))
  have freshness6 : nb056AlphaDummy000 ≠ nb056AlphaDummy011 :=
    by
    unfold nb056AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0165) 0))
  have freshness7 : f ≠ (nb056AlphaDummy012 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0167 f) 0))
  have freshness8 : nb056AlphaDummy000 ≠ nb056AlphaDummy003 :=
    by
    unfold nb056AlphaDummy003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0162) 0))
  have freshness9 : f ≠ (nb056AlphaDummy004 f) :=
    by
    unfold nb056AlphaDummy004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0163 f) 0))
  have freshness10 : nb056AlphaDummy000 ≠ nb056AlphaDummy001 :=
    by
    unfold nb056AlphaDummy001
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0160) 0))
  have freshness11 : f ≠ (nb056AlphaDummy002 f) :=
    by
    unfold nb056AlphaDummy002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0161 f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11 (TAlphaVar.here _ _ _))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0026`. -/
@[expose]
noncomputable def nb056SplitAlpha0026 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
        ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (synWbr (Class.cv (nb056AlphaDummy005))
          (synCcnv (Class.cv (nb056AlphaDummy000))) (Class.cv (nb056AlphaDummy007)))
        (Wff.neg (synWbr (Class.cv (nb056AlphaDummy007)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy006)))))
      (Wff.imp (synWbr (Class.cv (nb056AlphaDummy008 f)) (synCcnv (Class.cv f))
          (Class.cv (nb056AlphaDummy010 f))) (Wff.neg
          (synWbr (Class.cv (nb056AlphaDummy010 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy009 f))))) :=
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
        (((Class.cv (nb056AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb056SplitAlpha0006 f)))))
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
        (((Class.cv (nb056AlphaDummy000))).fv ∪ ((synCcnv
        (Class.cv (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪ ((synCcnv (Class.cv
        (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb056SplitAlpha0006 f)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb056SplitAlpha0009 f)))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0020 f))))))
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
                              (nb056SplitAlpha0022 f)))))
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
                              (nb056SplitAlpha0022 f)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb056SplitAlpha0025 f))))))))
        (nb056ComposeVariableOccurrence f))))

theorem nb056_wpp_notmem_0490 : (nb056AlphaDummy003) ∉ ((synCid)).fv := by
  simpa only [nb056AlphaDummy003, fv_syn_cid] using (nb056_compact_fv_empty_0026)

theorem nb056_wpp_notmem_0491 (f : Var) : (nb056AlphaDummy004 f) ∉ ((synCid)).fv := by
  simpa only [nb056AlphaDummy004, fv_syn_cid] using (nb056_compact_fv_empty_0027 f)

theorem nb056_wpp_notmem_0492 : (nb056AlphaDummy001) ∉ ((synCid)).fv := by
  simpa only [nb056AlphaDummy001, fv_syn_cid] using (nb056_compact_fv_empty_0028)

theorem nb056_wpp_notmem_0493 (f : Var) : (nb056AlphaDummy002 f) ∉ ((synCid)).fv := by
  simpa only [nb056AlphaDummy002, fv_syn_cid] using (nb056_compact_fv_empty_0029 f)

theorem nb056_wpp_notmem_0494 : (nb056AlphaDummy000) ∉ ((synCid)).fv := by
  simpa only [nb056AlphaDummy000, fv_syn_cid] using (nb056_compact_fv_empty_0030)

theorem nb056_wpp_notmem_0495 (f : Var) : f ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb056_compact_fv_empty_0031 f)

theorem nb056_compact_envfresh_0035 (f : Var) :
    TEnvFresh
      [((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
        ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
        ((nb056AlphaDummy000), f)]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb056AlphaDummy003) (nb056AlphaDummy004 f)
      (nb056_wpp_notmem_0490) (nb056_wpp_notmem_0491 f)
      (TEnvFresh.consFresh (nb056AlphaDummy001) (nb056AlphaDummy002 f)
        (nb056_wpp_notmem_0492) (nb056_wpp_notmem_0493 f)
        (TEnvFresh.consFresh (nb056AlphaDummy000) f (nb056_wpp_notmem_0494)
          (nb056_wpp_notmem_0495 f) (TEnvFresh.nil ((synCid)).fv))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
