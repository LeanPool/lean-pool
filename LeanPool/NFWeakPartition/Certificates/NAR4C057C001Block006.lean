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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0065`. -/
@[expose]
noncomputable def nb057SplitAlpha0065 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
        ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
        ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
        ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
        ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy144))
            (synCun (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy147 f))
            (synCun (Class.cv (nb057AlphaDummy148 f))
              (Class.cv (nb057AlphaDummy149 f)))))) :=
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
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
          ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
          ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
          ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
          ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
          ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
          ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
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
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0066`. -/
@[expose]
noncomputable def nb057SplitAlpha0066 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.classEq (Class.cv (nb057AlphaDummy130))
        (synCphi (Class.cv (nb057AlphaDummy131))))
      (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
        (synCphi (Class.cv (nb057AlphaDummy133 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057AlphaDummy126 f))).fv ∪
            ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057AlphaDummy131))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057AlphaDummy133 f))).fv) (by decide))
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
                                  (TAlphaClass.reflOfClosed
                                    [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
                                      ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
                                      ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
                                      ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                                      ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
                                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                                      ((nb057AlphaDummy000), a),
                                      ((nb057AlphaDummy001), f), ((nb057AlphaDummy002),
                                        (nb057AlphaDummy003 f a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057SplitAlpha0065 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                          ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                          ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                          ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
                          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                          ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                          ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                          ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
                          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0067`. -/
@[expose]
noncomputable def nb057SplitAlpha0067 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
        ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
        ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
        ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
        ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
        ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy144))
            (synCun (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy147 f))
            (synCun (Class.cv (nb057AlphaDummy148 f))
              (Class.cv (nb057AlphaDummy149 f)))))) :=
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
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
          ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
          ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
          ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
          ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
          ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
          ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
          ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
          ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
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
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0068`. -/
@[expose]
noncomputable def nb057SplitAlpha0068 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
        ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy138))
          (Class.cv (nb057AlphaDummy131))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy139))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))
              (Class.cv (nb057AlphaDummy138))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy140 f))
          (Class.cv (nb057AlphaDummy133 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy141 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))
              (Class.cv (nb057AlphaDummy140 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057AlphaDummy131))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy133 f))).fv) (by decide))
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
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
                                  ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
                                  ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
                                  ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                                  ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                                  ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                                  ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
                                  ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                                  ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                                  ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                                  ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                                  ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                                  ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                  ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                  ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                  ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                                  ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0067 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                      ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
                      ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                      ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                      ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
                      ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                      ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0069`. -/
@[expose]
noncomputable def nb057SplitAlpha0069 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy160))
          (Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy160))
            (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy161 f))
          (Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy161 f))
            (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                    (synCsn (synC0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy124))).fv ∪
                      ((Class.cv (nb057AlphaDummy125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy126 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0068 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0068 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                          ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
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
                      (((Class.cv (nb057AlphaDummy124))).fv ∪
                        ((Class.cv (nb057AlphaDummy125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy126 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0068 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0068 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                            ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                            ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                            ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                            ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                            ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                            ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                            ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                            ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                            ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0070`. -/
@[expose]
noncomputable def nb057SplitAlpha0070 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
        ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
        ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
        ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
        ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy180))
            (synCun (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy183 f))
            (synCun (Class.cv (nb057AlphaDummy184 f))
              (Class.cv (nb057AlphaDummy185 f)))))) :=
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
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
          ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
          ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
          ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
          ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
          ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
          ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
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
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0071`. -/
@[expose]
noncomputable def nb057SplitAlpha0071 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.classEq (Class.cv (nb057AlphaDummy166))
        (synCphi (Class.cv (nb057AlphaDummy167))))
      (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
        (synCphi (Class.cv (nb057AlphaDummy169 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057AlphaDummy127 f))).fv ∪
            ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057AlphaDummy167))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057AlphaDummy169 f))).fv) (by decide))
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
                                  (TAlphaClass.reflOfClosed
                                    [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
                                      ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
                                      ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
                                      ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                                      ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
                                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                                      ((nb057AlphaDummy000), a),
                                      ((nb057AlphaDummy001), f), ((nb057AlphaDummy002),
                                        (nb057AlphaDummy003 f a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057SplitAlpha0070 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                          ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                          ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                          ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
                          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                          ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                          ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                          ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
                          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0072`. -/
@[expose]
noncomputable def nb057SplitAlpha0072 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
        ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
        ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
        ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
        ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
        ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy180))
            (synCun (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy183 f))
            (synCun (Class.cv (nb057AlphaDummy184 f))
              (Class.cv (nb057AlphaDummy185 f)))))) :=
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
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
          ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
          ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
          ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
          ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
          ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
          ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
          ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
          ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
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
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0073`. -/
@[expose]
noncomputable def nb057SplitAlpha0073 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
        ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy174))
          (Class.cv (nb057AlphaDummy167))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy175))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))
              (Class.cv (nb057AlphaDummy174))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy176 f))
          (Class.cv (nb057AlphaDummy169 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy177 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))
              (Class.cv (nb057AlphaDummy176 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057AlphaDummy167))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy169 f))).fv) (by decide))
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
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
                                  ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
                                  ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
                                  ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                                  ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                                  ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                                  ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
                                  ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                                  ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                                  ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                                  ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                                  ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                                  ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                  ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                  ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                  ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                                  ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0072 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                      ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
                      ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                      ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                      ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
                      ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                      ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0074`. -/
@[expose]
noncomputable def nb057SplitAlpha0074 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy196))
          (Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy196))
            (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy197 f))
          (Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy197 f))
            (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                    (synCsn (synC0c))))))))) :=
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
                          (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy125))).fv ∪
                      ((Class.cv (nb057AlphaDummy124))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy127 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0073 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0073 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                          ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
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
                            (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy125))).fv ∪
                        ((Class.cv (nb057AlphaDummy124))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy127 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0073 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0073 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                            ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                            ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                            ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                            ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                            ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                            ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                            ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                            ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                            ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as
`nb057_final_composition_variable_occurrence`.
-/
@[expose]
noncomputable def nb057FinalCompositionVariableOccurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Class.cv (nb057AlphaDummy001)) (Class.cv f) :=
  by
  have freshness0 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy125) :=
    by
    unfold nb057AlphaDummy125
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 1))
  have freshness1 : f ≠ (nb057AlphaDummy127 f) :=
    by
    unfold nb057AlphaDummy127
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 1))
  have freshness2 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy124) :=
    by
    unfold nb057AlphaDummy124
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 0))
  have freshness3 : f ≠ (nb057AlphaDummy126 f) :=
    by
    unfold nb057AlphaDummy126
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 0))
  have freshness4 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy128) :=
    by
    unfold nb057AlphaDummy128
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0210) 0))
  have freshness5 : f ≠ (nb057AlphaDummy129 f) :=
    by
    unfold nb057AlphaDummy129
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0211 f) 0))
  have freshness6 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy239) :=
    by
    unfold nb057AlphaDummy239
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0290) 1))
  have freshness7 : f ≠ (nb057AlphaDummy241 f) :=
    by
    unfold nb057AlphaDummy241
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0291 f) 1))
  have freshness8 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy238) :=
    by
    unfold nb057AlphaDummy238
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0290) 0))
  have freshness9 : f ≠ (nb057AlphaDummy240 f) :=
    by
    unfold nb057AlphaDummy240
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0291 f) 0))
  have freshness10 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy000) :=
    by
    unfold nb057AlphaDummy001 nb057AlphaDummy000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness11 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11 (TAlphaVar.here _ _ _))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0075`. -/
@[expose]
noncomputable def nb057SplitAlpha0075 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq (Class.cv (nb057AlphaDummy128))
          (synCop (Class.cv (nb057AlphaDummy124)) (Class.cv (nb057AlphaDummy125))))
        (Wff.neg (synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))))
      (Wff.imp (Wff.classEq (Class.cv (nb057AlphaDummy129 f))
          (synCop (Class.cv (nb057AlphaDummy126 f)) (Class.cv (nb057AlphaDummy127 f))))
        (Wff.neg (synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f))))) :=
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
        (((Class.cv (nb057AlphaDummy001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (nb057SplitAlpha0066 f a)))))
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
        (((Class.cv (nb057AlphaDummy001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (nb057SplitAlpha0066 f a)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0069 f a)))))))))
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
                              (nb057SplitAlpha0071 f a)))))
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
                              (nb057SplitAlpha0071 f a)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0074 f a))))))))
        (nb057FinalCompositionVariableOccurrence f a dv_a_f))))

/-- Checked nominal proof certificate identified upstream as
`nb057_final_pair_binder_occurrence`.
-/
@[expose]
noncomputable def nb057FinalPairBinderOccurrence (f : Var) (a : Var) :
    TAlphaClass
      [((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Class.cv (nb057AlphaDummy050)) (Class.cv (nb057AlphaDummy051 f)) :=
  by
  have freshness0 : (nb057AlphaDummy050) ≠ (nb057AlphaDummy045) :=
    by
    unfold nb057AlphaDummy050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0044) 0)))
  have freshness1 : (nb057AlphaDummy051 f) ≠ (nb057AlphaDummy048 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0045 f) 0)))
  have freshness2 : (nb057AlphaDummy050) ≠ (nb057AlphaDummy044) :=
    by
    unfold nb057AlphaDummy050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0042) 0)))
  have freshness3 : (nb057AlphaDummy051 f) ≠ (nb057AlphaDummy047 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0043 f) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0076`. -/
@[expose]
noncomputable def nb057SplitAlpha0076 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (synWfun (Class.cv (nb057AlphaDummy001))) (Wff.neg
          (Wff.classEq (synCdm (Class.cv (nb057AlphaDummy001)))
            (Class.cv (nb057AlphaDummy000)))))
      (Wff.imp (synWfun (Class.cv f))
        (Wff.neg (Wff.classEq (synCdm (Class.cv f)) (Class.cv a)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0032 f a dv_a_f)))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classEq (nb057FinalPairBinderOccurrence f a) (TAlphaClass.cab
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
        (nb057AlphaDummy001))).fv ∪ ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb057SplitAlpha0034 f a)))))
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
        (nb057AlphaDummy001))).fv ∪ ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (nb057SplitAlpha0034 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb057SplitAlpha0037 f a)))))))))
              (TAlphaWff.ex (TAlphaWff.neg (nb057SplitAlpha0059 f a dv_a_f))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                    ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                    ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                    ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                  (synCvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0061 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0061 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.neg (nb057SplitAlpha0064 f a)))))))) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex
                      (TAlphaWff.neg (nb057SplitAlpha0075 f a dv_a_f)))))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _)))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_fns`. -/
@[expose]
noncomputable def nominalDfFns (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    Nominal.NPrf (.classEq (synCfns) (synCopab f a (synWfn (.cv f) (.cv a)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb057SplitAlpha0004 f a dv_a_f)
              (TAlphaWff.neg (nb057SplitAlpha0076 f a dv_a_f))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
