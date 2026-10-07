/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part013`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0010`. -/
@[expose]
noncomputable def nb067SplitAlpha0010 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
        ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
        ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
        ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
        ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy105))
            (synCun (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy108 f))
            (synCun (Class.cv (nb067AlphaDummy109 f))
              (Class.cv (nb067AlphaDummy110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0111 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0109 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0115 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0113 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0111 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0109 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0115 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0113 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
          ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
          ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
          ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
          ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
          ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
          ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0119 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0117 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0119 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0117 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0123 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0121 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0123 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0121 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0011`. -/
@[expose]
noncomputable def nb067SplitAlpha0011 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy099))
          (Class.cv (nb067AlphaDummy092))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy100))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))
              (Class.cv (nb067AlphaDummy099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy101 f))
          (Class.cv (nb067AlphaDummy094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy102 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))
              (Class.cv (nb067AlphaDummy101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0106) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0107 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0106) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0107 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0104) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
                                  ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
                                  ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
                                  ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                                  ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                                  ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                                  ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                                  ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                                  ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
                                  ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0010 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                      ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                      ((nb067AlphaDummy097), (nb067AlphaDummy098 f)),
                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0012`. -/
@[expose]
noncomputable def nb067SplitAlpha0012 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
        ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
        ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
        ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
        ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
        ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy105))
            (synCun (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy108 f))
            (synCun (Class.cv (nb067AlphaDummy109 f))
              (Class.cv (nb067AlphaDummy110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0111 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0109 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0115 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0113 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0111 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0109 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0115 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0113 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
          ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
          ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
          ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
          ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
          ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
          ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
          ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
          ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0119 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0117 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0119 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0117 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0123 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0121 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0123 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0121 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part014`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0013`. -/
@[expose]
noncomputable def nb067SplitAlpha0013 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
        ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
        ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
        ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
        ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
        ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
        ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy099))
          (Class.cv (nb067AlphaDummy092))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy100))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))
              (Class.cv (nb067AlphaDummy099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy101 f))
          (Class.cv (nb067AlphaDummy094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy102 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))
              (Class.cv (nb067AlphaDummy101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0132) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0133 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0130) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0131 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0106) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0107 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0106) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0107 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0104) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy107), (nb067AlphaDummy110 f)),
                                  ((nb067AlphaDummy106), (nb067AlphaDummy109 f)),
                                  ((nb067AlphaDummy105), (nb067AlphaDummy108 f)),
                                  ((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                                  ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                                  ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                                  ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
                                  ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                                  ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                                  ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                                  ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                                  ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0012 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                      ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
                      ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                      ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy103), (nb067AlphaDummy104 f)),
                      ((nb067AlphaDummy099), (nb067AlphaDummy101 f)),
                      ((nb067AlphaDummy100), (nb067AlphaDummy102 f)),
                      ((nb067AlphaDummy125), (nb067AlphaDummy126 f)),
                      ((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                      ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                      ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                      ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                      ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0014`. -/
@[expose]
noncomputable def nb067SplitAlpha0014 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
        ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy121))
          (Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy121))
            (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy122 f))
          (Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy122 f))
            (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0128) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0129 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0125) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0127 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
                      ((Class.cv (nb067AlphaDummy084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0013 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067SplitAlpha0013 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                          ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                          ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                          ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                          ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0128) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0129 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0125) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0127 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy083))).fv ∪
                        ((Class.cv (nb067AlphaDummy084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0013 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067SplitAlpha0013 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy123), (nb067AlphaDummy124 f)),
                            ((nb067AlphaDummy092), (nb067AlphaDummy094 f)),
                            ((nb067AlphaDummy091), (nb067AlphaDummy093 f)),
                            ((nb067AlphaDummy121), (nb067AlphaDummy122 f)),
                            ((nb067AlphaDummy095), (nb067AlphaDummy096 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                            ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0015`. -/
@[expose]
noncomputable def nb067SplitAlpha0015 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
        ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
        ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
        ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
        ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy141))
            (synCun (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy144 f))
            (synCun (Class.cv (nb067AlphaDummy145 f))
              (Class.cv (nb067AlphaDummy146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0149 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0147 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0149 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0147 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
          ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
          ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
          ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
          ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
          ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
          ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
          ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
          ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
          ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0161 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0159 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0161 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0159 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part015`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0016`. -/
@[expose]
noncomputable def nb067SplitAlpha0016 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy135))
          (Class.cv (nb067AlphaDummy128))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy136))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))
              (Class.cv (nb067AlphaDummy135))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy137 f))
          (Class.cv (nb067AlphaDummy130 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy138 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))
              (Class.cv (nb067AlphaDummy137 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0144) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0145 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0144) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0145 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0142) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
                                  ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
                                  ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
                                  ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                                  ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                                  ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                                  ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                                  ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                                  ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
                                  ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0015 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                      ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                      ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                      ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                      ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                      ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
                      ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                      ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                      ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                      ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                      ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                      ((nb067AlphaDummy133), (nb067AlphaDummy134 f)),
                      ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0017`. -/
@[expose]
noncomputable def nb067SplitAlpha0017 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
        ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
        ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
        ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
        ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
        ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy141))
            (synCun (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy144 f))
            (synCun (Class.cv (nb067AlphaDummy145 f))
              (Class.cv (nb067AlphaDummy146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0149 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0147 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0149 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0147 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
          ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
          ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
          ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
          ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
          ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
          ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
          ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
          ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
          ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
          ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
          ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0161 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0159 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0161 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0159 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0018`. -/
@[expose]
noncomputable def nb067SplitAlpha0018 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
        ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
        ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
        ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
        ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
        ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
        ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy136))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))
          (Class.cv (nb067AlphaDummy135))))
      (Wff.classEq (Class.cv (nb067AlphaDummy138 f))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))
          (Class.cv (nb067AlphaDummy137 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy128))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067AlphaDummy130 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0144) 1))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0145 f) 1))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy143), (nb067AlphaDummy146 f)),
                              ((nb067AlphaDummy142), (nb067AlphaDummy145 f)),
                              ((nb067AlphaDummy141), (nb067AlphaDummy144 f)),
                              ((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                              ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                              ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                              ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
                              ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                              ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                              ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                              ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                              ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                              ((nb067AlphaDummy000), f),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067SplitAlpha0017 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                  ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                  ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                  ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
                  ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                  ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                  ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                  ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                  ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy139), (nb067AlphaDummy140 f)),
                  ((nb067AlphaDummy135), (nb067AlphaDummy137 f)),
                  ((nb067AlphaDummy136), (nb067AlphaDummy138 f)),
                  ((nb067AlphaDummy161), (nb067AlphaDummy162 f)),
                  ((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                  ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                  ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                  ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                  ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0019`. -/
@[expose]
noncomputable def nb067SplitAlpha0019 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
        ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy157))
          (Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy157))
            (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy158 f))
          (Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy158 f))
            (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0166) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0167 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0163) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0165 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy083))).fv ∪
                      ((Class.cv (nb067AlphaDummy085))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy088 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0140) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0140) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0141 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0169 f) 0)) (TAlphaVar.here _ _ _)))))))
                                    (nb067SplitAlpha0018 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0140) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0141 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0140) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0141 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0169 f) 0)) (TAlphaVar.here _ _ _)))))))
                                    (nb067SplitAlpha0018 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                          ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                          ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                          ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                          ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0166) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0167 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0163) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0165 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy083))).fv ∪
                        ((Class.cv (nb067AlphaDummy085))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy086 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy088 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0141 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0169 f) 0)) (TAlphaVar.here _ _ _)))))))
                                      (nb067SplitAlpha0018 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0141 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0170) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0171 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0168) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0169 f) 0)) (TAlphaVar.here _ _ _)))))))
                                      (nb067SplitAlpha0018 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy159), (nb067AlphaDummy160 f)),
                            ((nb067AlphaDummy128), (nb067AlphaDummy130 f)),
                            ((nb067AlphaDummy127), (nb067AlphaDummy129 f)),
                            ((nb067AlphaDummy157), (nb067AlphaDummy158 f)),
                            ((nb067AlphaDummy131), (nb067AlphaDummy132 f)),
                            ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                            ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part016`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0020`. -/
@[expose]
noncomputable def nb067SplitAlpha0020 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
        ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
        ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
        ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy183))
            (synCun (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy186 f))
            (synCun (Class.cv (nb067AlphaDummy187 f))
              (Class.cv (nb067AlphaDummy188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
          ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0021`. -/
@[expose]
noncomputable def nb067SplitAlpha0021 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy178))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))
          (Class.cv (nb067AlphaDummy177))))
      (Wff.classEq (Class.cv (nb067AlphaDummy180 f))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))
          (Class.cv (nb067AlphaDummy179 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy170))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 1))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 1))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
                              ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
                              ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
                              ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                              ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                              ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                              ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                              ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                              ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                              ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                              ((nb067AlphaDummy000), f),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067SplitAlpha0020 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                  ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                  ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                  ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                  ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                  ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                  ((nb067AlphaDummy175), (nb067AlphaDummy176 f)),
                  ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part017`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0022`. -/
@[expose]
noncomputable def nb067SplitAlpha0022 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
        ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
        ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
        ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
        ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy183))
            (synCun (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy186 f))
            (synCun (Class.cv (nb067AlphaDummy187 f))
              (Class.cv (nb067AlphaDummy188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
          ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
          ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0023`. -/
@[expose]
noncomputable def nb067SplitAlpha0023 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
        ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
        ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
        ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
        ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
        ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
        ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
        ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy181))
              (synCplc (Class.cv (nb067AlphaDummy177)) (synC1c)))
            (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb067AlphaDummy181)) (Class.cv (nb067AlphaDummy177)))
          (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy182 f))
              (synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb067AlphaDummy182 f))
            (Class.cv (nb067AlphaDummy179 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy185), (nb067AlphaDummy188 f)),
                          ((nb067AlphaDummy184), (nb067AlphaDummy187 f)),
                          ((nb067AlphaDummy183), (nb067AlphaDummy186 f)),
                          ((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
                          ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
                          ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
                          ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
                          ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb067SplitAlpha0022 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
              ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
              ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
              ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
              ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
              ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
              ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
              ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
              ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
              ((nb067AlphaDummy000), f),
              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb067AlphaDummy181), (nb067AlphaDummy182 f)),
              ((nb067AlphaDummy177), (nb067AlphaDummy179 f)),
              ((nb067AlphaDummy178), (nb067AlphaDummy180 f)),
              ((nb067AlphaDummy203), (nb067AlphaDummy204 f)),
              ((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
              ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
              ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
              ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
              ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
              ((nb067AlphaDummy000), f),
              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0024`. -/
@[expose]
noncomputable def nb067SplitAlpha0024 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
        ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy199))
          (Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy199))
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy200 f))
          (Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067AlphaDummy200 f))
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0208) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0209 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0205) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0207 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy163))).fv ∪
                      ((Class.cv (nb067AlphaDummy164))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                      ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb067SplitAlpha0023 x y f)))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb067SplitAlpha0023 x y f)))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                          ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                          ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                          ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                          ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0208) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0209 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0205) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0207 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067AlphaDummy163))).fv ∪
                        ((Class.cv (nb067AlphaDummy164))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067AlphaDummy165 f))).fv ∪
                        ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (nb067SplitAlpha0023 x y f)))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0183 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0182) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0183 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0212) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0213 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0210) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0211 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067AlphaDummy172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab
        (nb067SplitAlpha0023 x y f)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb067AlphaDummy201), (nb067AlphaDummy202 f)),
                            ((nb067AlphaDummy170), (nb067AlphaDummy172 f)),
                            ((nb067AlphaDummy169), (nb067AlphaDummy171 f)),
                            ((nb067AlphaDummy199), (nb067AlphaDummy200 f)),
                            ((nb067AlphaDummy173), (nb067AlphaDummy174 f)),
                            ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                            ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                            ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                            ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                            ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                            ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                            ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                            ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                            ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                            ((nb067AlphaDummy000), f),
                            ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                            ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                            ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part018`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0025`. -/
@[expose]
noncomputable def nb067SplitAlpha0025 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
        ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
        ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
        ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
        ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy219))
            (synCun (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy222 f))
            (synCun (Class.cv (nb067AlphaDummy223 f))
              (Class.cv (nb067AlphaDummy224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
          ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
          ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
          ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
          ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
          ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
          ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0026`. -/
@[expose]
noncomputable def nb067SplitAlpha0026 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy214))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))
          (Class.cv (nb067AlphaDummy213))))
      (Wff.classEq (Class.cv (nb067AlphaDummy216 f))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))
          (Class.cv (nb067AlphaDummy215 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0224) 1))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0225 f) 1))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0224) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0225 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
                              ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
                              ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
                              ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                              ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                              ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                              ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                              ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                              ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
                              ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                              ((nb067AlphaDummy000), f),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067SplitAlpha0025 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                  ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                  ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                  ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                  ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                  ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
                  ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                  ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                  ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                  ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                  ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                  ((nb067AlphaDummy211), (nb067AlphaDummy212 f)),
                  ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                  ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                  ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                  ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0027`. -/
@[expose]
noncomputable def nb067SplitAlpha0027 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
        ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
        ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
        ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
        ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
        ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy219))
            (synCun (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy222 f))
            (synCun (Class.cv (nb067AlphaDummy223 f))
              (Class.cv (nb067AlphaDummy224 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
          ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
          ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
          ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
          ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
          ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
          ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
          ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
          ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part019`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0028`. -/
@[expose]
noncomputable def nb067SplitAlpha0028 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
        ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
        ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
        ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
        ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
        ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy217))
              (synCplc (Class.cv (nb067AlphaDummy213)) (synC1c)))
            (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb067AlphaDummy217)) (Class.cv (nb067AlphaDummy213)))
          (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy218 f))
              (synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb067AlphaDummy218 f))
            (Class.cv (nb067AlphaDummy215 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0224) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0225 f) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0224) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0225 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb067AlphaDummy221), (nb067AlphaDummy224 f)),
                          ((nb067AlphaDummy220), (nb067AlphaDummy223 f)),
                          ((nb067AlphaDummy219), (nb067AlphaDummy222 f)),
                          ((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
                          ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
                          ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
                          ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
                          ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                          ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                          ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                          ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                          ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                          ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                          ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                          ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                          ((nb067AlphaDummy000), f),
                          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb067SplitAlpha0027 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
              ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
              ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
              ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
              ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
              ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
              ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
              ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
              ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
              ((nb067AlphaDummy000), f),
              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb067AlphaDummy217), (nb067AlphaDummy218 f)),
              ((nb067AlphaDummy213), (nb067AlphaDummy215 f)),
              ((nb067AlphaDummy214), (nb067AlphaDummy216 f)),
              ((nb067AlphaDummy239), (nb067AlphaDummy240 f)),
              ((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
              ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
              ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
              ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
              ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
              ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
              ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
              ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
              ((nb067AlphaDummy000), f),
              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0029`. -/
@[expose]
noncomputable def nb067SplitAlpha0029 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
        ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
        ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
        ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
        ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy206))
            (Class.cv (nb067AlphaDummy163))) (Wff.classEq (Class.cv (nb067AlphaDummy205))
            (synCun (synCphi (Class.cv (nb067AlphaDummy206))) (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb067AlphaDummy208 f))
            (Class.cv (nb067AlphaDummy165 f)))
          (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
            (synCun (synCphi (Class.cv (nb067AlphaDummy208 f))) (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0246) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0247 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0243) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0245 f) 0)) (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb067AlphaDummy000))).fv) (by decide))
                    (freshVar_injective (((Class.cv f)).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb067AlphaDummy164))).fv ∪
                ((Class.cv (nb067AlphaDummy163))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0220) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0221 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0220) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0221 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0250) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0251 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0248) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0249 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb067SplitAlpha0028 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0220) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0221 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0220) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0221 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0250) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0251 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0248) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0249 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy206))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067AlphaDummy208 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb067SplitAlpha0028 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb067AlphaDummy237), (nb067AlphaDummy238 f)),
                    ((nb067AlphaDummy206), (nb067AlphaDummy208 f)),
                    ((nb067AlphaDummy205), (nb067AlphaDummy207 f)),
                    ((nb067AlphaDummy235), (nb067AlphaDummy236 f)),
                    ((nb067AlphaDummy209), (nb067AlphaDummy210 f)),
                    ((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
                    ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
                    ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
                    ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                    ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                    ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                    ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                    ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                    ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                    ((nb067AlphaDummy000), f),
                    ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                    ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                    ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_function_occurrence`. -/
@[expose]
noncomputable def nb067FunctionOccurrence (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Class.cv (nb067AlphaDummy000)) (Class.cv f) :=
  by
  have freshness0 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy164) :=
    by
    unfold nb067AlphaDummy164
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 1))
  have freshness1 : f ≠ (nb067AlphaDummy166 f) :=
    by
    unfold nb067AlphaDummy166
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 1))
  have freshness2 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy163) :=
    by
    unfold nb067AlphaDummy163
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 0))
  have freshness3 : f ≠ (nb067AlphaDummy165 f) :=
    by
    unfold nb067AlphaDummy165
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 0))
  have freshness4 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy167) :=
    by
    unfold nb067AlphaDummy167
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0260) 0))
  have freshness5 : f ≠ (nb067AlphaDummy168 f) :=
    by
    unfold nb067AlphaDummy168
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0261 f) 0))
  have freshness6 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy085) :=
    by
    unfold nb067AlphaDummy085
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))
  have freshness7 : f ≠ (nb067AlphaDummy088 f) :=
    by
    unfold nb067AlphaDummy088
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))
  have freshness8 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy084) :=
    by
    unfold nb067AlphaDummy084
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))
  have freshness9 : f ≠ (nb067AlphaDummy087 f) :=
    by
    unfold nb067AlphaDummy087
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 1))
  have freshness10 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy083) :=
    by
    unfold nb067AlphaDummy083
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 0))
  have freshness11 : f ≠ (nb067AlphaDummy086 f) :=
    by
    unfold nb067AlphaDummy086
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 0))
  have freshness12 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy089) :=
    by
    unfold nb067AlphaDummy089
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0257) 0))
  have freshness13 : f ≠ (nb067AlphaDummy090 f) :=
    by
    unfold nb067AlphaDummy090
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0259 f) 0))
  have freshness14 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy081) :=
    by
    unfold nb067AlphaDummy081
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0254) 0))
  have freshness15 : f ≠ (nb067AlphaDummy082 f) :=
    by
    unfold nb067AlphaDummy082
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0255 f) 0))
  have freshness16 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy079) :=
    by
    unfold nb067AlphaDummy079
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0252) 0))
  have freshness17 : f ≠ (nb067AlphaDummy080 f) :=
    by
    unfold nb067AlphaDummy080
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0253 f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15
                        (TAlphaVar.there freshness16 freshness17
                          (TAlphaVar.here _ _ _)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0030`. -/
@[expose]
noncomputable def nb067SplitAlpha0030 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy164), (nb067AlphaDummy166 f)),
        ((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classMem
        (synCop (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy163)))
        (Class.cv (nb067AlphaDummy000)))
      (Wff.classMem (synCop (Class.cv (nb067AlphaDummy166 f))
          (Class.cv (nb067AlphaDummy165 f))) (Class.cv f)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0214) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0214) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0218) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0219 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0215) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0217 f) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy164))).fv ∪
                                    ((Class.cv (nb067AlphaDummy163))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                                    ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 1)) (TAlphaVar.here _ _ _)))))
                                  (nb067SplitAlpha0026 x y f)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0214) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0214) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0218) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0219 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0215) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0217 f) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy164))).fv ∪
                                    ((Class.cv (nb067AlphaDummy163))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb067AlphaDummy166 f))).fv ∪
                                    ((Class.cv (nb067AlphaDummy165 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 1)) (TAlphaVar.here _ _ _)))))
                                  (nb067SplitAlpha0026 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb067SplitAlpha0029 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb067SplitAlpha0029 x y f))))))))))))
    (nb067FunctionOccurrence x y f))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0031`. -/
@[expose]
noncomputable def nb067SplitAlpha0031 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy163), (nb067AlphaDummy165 f)),
        ((nb067AlphaDummy167), (nb067AlphaDummy168 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.all (nb067AlphaDummy164) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb067AlphaDummy167))
              (synCop (Class.cv (nb067AlphaDummy163)) (Class.cv (nb067AlphaDummy164))))
            (synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
              (Class.cv (nb067AlphaDummy163))))))
      (Wff.all (nb067AlphaDummy166 f) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb067AlphaDummy168 f))
              (synCop (Class.cv (nb067AlphaDummy165 f))
                (Class.cv (nb067AlphaDummy166 f))))
            (synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
              (Class.cv (nb067AlphaDummy165 f)))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0174) 0)))
              (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0175 f) 0)))
              (TAlphaVar.there
                (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0172) 0)))
                (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0173 f) 0)))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0176) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0176) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0178 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0180) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0181 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0177) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0179 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb067AlphaDummy163))).fv ∪
        ((Class.cv (nb067AlphaDummy164))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb067AlphaDummy165 f))).fv ∪
        ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 1)) (TAlphaVar.here _ _ _)))))
                                        (nb067SplitAlpha0021 x y f)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0176) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0176) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0178 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0180) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0181 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0177) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0179 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb067AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb067AlphaDummy163))).fv ∪
        ((Class.cv (nb067AlphaDummy164))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb067AlphaDummy165 f))).fv ∪
        ((Class.cv (nb067AlphaDummy166 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 1)) (TAlphaVar.here _ _ _)))))
                                        (nb067SplitAlpha0021 x y f)))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb067SplitAlpha0024 x y f)))))))))
        (nb067SplitAlpha0030 x y f))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0032`. -/
@[expose]
noncomputable def nb067SplitAlpha0032 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
        ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
        ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
        ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
        ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy255))
            (synCun (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy258 f))
            (synCun (Class.cv (nb067AlphaDummy259 f))
              (Class.cv (nb067AlphaDummy260 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0278) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0279 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0276) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0277 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0282) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0283 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0280) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0281 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0278) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0279 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0276) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0277 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0282) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0283 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0280) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0281 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
          ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
          ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
          ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
          ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
          ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
          ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
          ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
          ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
          ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0286) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0287 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0284) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0285 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0286) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0287 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0284) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0285 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0290) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0291 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0288) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0289 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0290) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0291 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0288) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0289 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part020`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0033`. -/
@[expose]
noncomputable def nb067SplitAlpha0033 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy249))
          (Class.cv (nb067AlphaDummy242))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy250))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))
              (Class.cv (nb067AlphaDummy249))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067AlphaDummy251 f))
          (Class.cv (nb067AlphaDummy244 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy252 f))
            (synCif (Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))
              (synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))
              (Class.cv (nb067AlphaDummy251 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy242))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067AlphaDummy244 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0274) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0275 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0274) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0275 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0272) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
                                  ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
                                  ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
                                  ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                                  ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                                  ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                                  ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                                  ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                                  ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
                                  ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                                  ((nb067AlphaDummy000), f), ((nb067AlphaDummy003),
                                    (nb067AlphaDummy004 x y f)),
                                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067SplitAlpha0032 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                      ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                      ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                      ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                      ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                      ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
                      ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                      ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                      ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                      ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                      ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                      ((nb067AlphaDummy247), (nb067AlphaDummy248 f)),
                      ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                      ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                      ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                      ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                      ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                      ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                      ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                      ((nb067AlphaDummy000), f),
                      ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                      ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                      ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0034`. -/
@[expose]
noncomputable def nb067SplitAlpha0034 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
        ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
        ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
        ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
        ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
        ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb067AlphaDummy255))
            (synCun (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067AlphaDummy258 f))
            (synCun (Class.cv (nb067AlphaDummy259 f))
              (Class.cv (nb067AlphaDummy260 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0278) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0279 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0276) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0277 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0282) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0283 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0280) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0281 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0278) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0279 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0276) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0277 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0282) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0283 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0280) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0281 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
          ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
          ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
          ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
          ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
          ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
          ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
          ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
          ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
          ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
          ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
          ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
          ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
          ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
          ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
          ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
          ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
          ((nb067AlphaDummy079), (nb067AlphaDummy080 f)), ((nb067AlphaDummy000), f),
          ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
          ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
          ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0286) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0287 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0284) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0285 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0286) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0287 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0284) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0285 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0290) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0291 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0288) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0289 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0290) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0291 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0288) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0289 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb067_split_alpha_0035`. -/
@[expose]
noncomputable def nb067SplitAlpha0035 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
        ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
        ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
        ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
        ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
        ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
        ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
        ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
        ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
        ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
        ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
        ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
        ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
        ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
        ((nb067AlphaDummy000), f),
        ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
        ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
        ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
      (Wff.classEq (Class.cv (nb067AlphaDummy250))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))
          (Class.cv (nb067AlphaDummy249))))
      (Wff.classEq (Class.cv (nb067AlphaDummy252 f))
        (synCif (Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))
          (synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))
          (Class.cv (nb067AlphaDummy251 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067AlphaDummy242))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067AlphaDummy244 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0274) 1))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0275 f) 1))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb067AlphaDummy257), (nb067AlphaDummy260 f)),
                              ((nb067AlphaDummy256), (nb067AlphaDummy259 f)),
                              ((nb067AlphaDummy255), (nb067AlphaDummy258 f)),
                              ((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                              ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                              ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                              ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
                              ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                              ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                              ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                              ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                              ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                              ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                              ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                              ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                              ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                              ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                              ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                              ((nb067AlphaDummy000), f),
                              ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                              ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                              ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067SplitAlpha0034 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                  ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                  ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                  ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
                  ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                  ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                  ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                  ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                  ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb067AlphaDummy253), (nb067AlphaDummy254 f)),
                  ((nb067AlphaDummy249), (nb067AlphaDummy251 f)),
                  ((nb067AlphaDummy250), (nb067AlphaDummy252 f)),
                  ((nb067AlphaDummy275), (nb067AlphaDummy276 f)),
                  ((nb067AlphaDummy273), (nb067AlphaDummy274 f)),
                  ((nb067AlphaDummy242), (nb067AlphaDummy244 f)),
                  ((nb067AlphaDummy241), (nb067AlphaDummy243 f)),
                  ((nb067AlphaDummy271), (nb067AlphaDummy272 f)),
                  ((nb067AlphaDummy245), (nb067AlphaDummy246 f)),
                  ((nb067AlphaDummy085), (nb067AlphaDummy088 f)),
                  ((nb067AlphaDummy084), (nb067AlphaDummy087 f)),
                  ((nb067AlphaDummy083), (nb067AlphaDummy086 f)),
                  ((nb067AlphaDummy089), (nb067AlphaDummy090 f)),
                  ((nb067AlphaDummy081), (nb067AlphaDummy082 f)),
                  ((nb067AlphaDummy079), (nb067AlphaDummy080 f)),
                  ((nb067AlphaDummy000), f),
                  ((nb067AlphaDummy003), (nb067AlphaDummy004 x y f)),
                  ((nb067AlphaDummy002), y), ((nb067AlphaDummy001), x),
                  ((nb067AlphaDummy005), (nb067AlphaDummy006 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
