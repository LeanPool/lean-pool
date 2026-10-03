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

@[expose]
noncomputable def nb067_split_alpha_0010 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
        ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
        ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
        ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
        ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_105))
            (syn_cun (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_108 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_109 f))
              (Class.cv (nb067_alpha_dummy_110 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0115 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0113 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
          ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
          ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
          ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
          ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
          ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
          ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0119 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0117 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0011 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_099))
          (Class.cv (nb067_alpha_dummy_092))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_100))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f))
          (Class.cv (nb067_alpha_dummy_094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_102 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0102) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0103 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
                                  ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
                                  ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
                                  ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                                  ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                                  ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                                  ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                                  ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                                  ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
                                  ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0010 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                      ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                      ((nb067_alpha_dummy_097), (nb067_alpha_dummy_098 f)),
                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0012 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
        ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
        ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
        ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
        ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
        ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_105))
            (syn_cun (Class.cv (nb067_alpha_dummy_106)) (Class.cv (nb067_alpha_dummy_107))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_109 f))
            (Class.cv (nb067_alpha_dummy_110 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_108 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_109 f))
              (Class.cv (nb067_alpha_dummy_110 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0115 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0113 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
          ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
          ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
          ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
          ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
          ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
          ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
          ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
          ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0119 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0117 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0013 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
        ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
        ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
        ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
        ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
        ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
        ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_099))
          (Class.cv (nb067_alpha_dummy_092))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_100))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_099)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_099)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f))
          (Class.cv (nb067_alpha_dummy_094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_102 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_101 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_101 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_101 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_094 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_107), (nb067_alpha_dummy_110 f)),
                                  ((nb067_alpha_dummy_106), (nb067_alpha_dummy_109 f)),
                                  ((nb067_alpha_dummy_105), (nb067_alpha_dummy_108 f)),
                                  ((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                                  ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                                  ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                                  ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
                                  ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                                  ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                                  ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                                  ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                                  ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0012 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                      ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
                      ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                      ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0105 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_103), (nb067_alpha_dummy_104 f)),
                      ((nb067_alpha_dummy_099), (nb067_alpha_dummy_101 f)),
                      ((nb067_alpha_dummy_100), (nb067_alpha_dummy_102 f)),
                      ((nb067_alpha_dummy_125), (nb067_alpha_dummy_126 f)),
                      ((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                      ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                      ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                      ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                      ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0014 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
        ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_121))
          (Class.cab (nb067_alpha_dummy_091)
            (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_121))
            (Class.cab (nb067_alpha_dummy_091)
              (syn_wrex (nb067_alpha_dummy_092) (Class.cv (nb067_alpha_dummy_084))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_122 f))
          (Class.cab (nb067_alpha_dummy_093 f)
            (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_122 f))
            (Class.cab (nb067_alpha_dummy_093 f)
              (syn_wrex (nb067_alpha_dummy_094 f) (Class.cv (nb067_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0013 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0013 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                          ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                          ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                          ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                          ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                      (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_084))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0013 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0013 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_123), (nb067_alpha_dummy_124 f)),
                            ((nb067_alpha_dummy_092), (nb067_alpha_dummy_094 f)),
                            ((nb067_alpha_dummy_091), (nb067_alpha_dummy_093 f)),
                            ((nb067_alpha_dummy_121), (nb067_alpha_dummy_122 f)),
                            ((nb067_alpha_dummy_095), (nb067_alpha_dummy_096 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                            ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0015 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
        ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
        ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
        ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
        ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_141))
            (syn_cun (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_144 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_145 f))
              (Class.cv (nb067_alpha_dummy_146 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
          ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
          ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
          ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
          ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
          ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
          ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
          ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
          ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
          ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0016 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_135))
          (Class.cv (nb067_alpha_dummy_128))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_136))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_135))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f))
          (Class.cv (nb067_alpha_dummy_130 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_138 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_137 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0140) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0141 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_130 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
                                  ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
                                  ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
                                  ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                                  ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                                  ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                                  ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                                  ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                                  ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
                                  ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0015 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                      ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                      ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                      ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                      ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                      ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
                      ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                      ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                      ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                      ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                      ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                      ((nb067_alpha_dummy_133), (nb067_alpha_dummy_134 f)),
                      ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0017 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
        ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
        ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
        ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
        ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
        ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_141))
            (syn_cun (Class.cv (nb067_alpha_dummy_142)) (Class.cv (nb067_alpha_dummy_143))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_145 f))
            (Class.cv (nb067_alpha_dummy_146 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_144 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_145 f))
              (Class.cv (nb067_alpha_dummy_146 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0151 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
          ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
          ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
          ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
          ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
          ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
          ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
          ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
          ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
          ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
          ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
          ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0157 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0155 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0018 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
        ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
        ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
        ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
        ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
        ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
        ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_136))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_135)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_135)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_135))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_138 f))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_137 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_137 f)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_137 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_128))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_130 f))).fv) (by decide))
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
                          (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_143), (nb067_alpha_dummy_146 f)),
                              ((nb067_alpha_dummy_142), (nb067_alpha_dummy_145 f)),
                              ((nb067_alpha_dummy_141), (nb067_alpha_dummy_144 f)),
                              ((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                              ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                              ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                              ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
                              ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                              ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                              ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                              ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                              ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                              ((nb067_alpha_dummy_000), f),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067_split_alpha_0017 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                  ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                  ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                  ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
                  ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                  ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                  ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                  ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                  ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0142) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0143 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_139), (nb067_alpha_dummy_140 f)),
                  ((nb067_alpha_dummy_135), (nb067_alpha_dummy_137 f)),
                  ((nb067_alpha_dummy_136), (nb067_alpha_dummy_138 f)),
                  ((nb067_alpha_dummy_161), (nb067_alpha_dummy_162 f)),
                  ((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                  ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                  ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                  ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                  ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb067_split_alpha_0019 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
        ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_157))
          (Class.cab (nb067_alpha_dummy_127)
            (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_157))
            (Class.cab (nb067_alpha_dummy_127)
              (syn_wrex (nb067_alpha_dummy_128) (Class.cv (nb067_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_158 f))
          (Class.cab (nb067_alpha_dummy_129 f)
            (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_158 f))
            (Class.cab (nb067_alpha_dummy_129 f)
              (syn_wrex (nb067_alpha_dummy_130 f) (Class.cv (nb067_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
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
                                    (nb067_split_alpha_0018 x y f)))))
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
                                    (nb067_split_alpha_0018 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                          ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                          ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                          ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                          ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                      (((Class.cv (nb067_alpha_dummy_083))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_085))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_086 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_088 f))).fv) (by decide))
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
                                      (nb067_split_alpha_0018 x y f)))))
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
                                      (nb067_split_alpha_0018 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_159), (nb067_alpha_dummy_160 f)),
                            ((nb067_alpha_dummy_128), (nb067_alpha_dummy_130 f)),
                            ((nb067_alpha_dummy_127), (nb067_alpha_dummy_129 f)),
                            ((nb067_alpha_dummy_157), (nb067_alpha_dummy_158 f)),
                            ((nb067_alpha_dummy_131), (nb067_alpha_dummy_132 f)),
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                            ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
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

@[expose]
noncomputable def nb067_split_alpha_0020 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
        ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
        ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
        ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183))
            (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_187 f))
              (Class.cv (nb067_alpha_dummy_188 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
          ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0021 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_178))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_177))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_180 f))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_179 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide))
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
                          (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
                              ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
                              ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
                              ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                              ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                              ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                              ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                              ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                              ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                              ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                              ((nb067_alpha_dummy_000), f),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067_split_alpha_0020 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                  ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                  ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                  ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                  ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                  ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                  ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)),
                  ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))


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

@[expose]
noncomputable def nb067_split_alpha_0022 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
        ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
        ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
        ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
        ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183))
            (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f))
            (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_187 f))
              (Class.cv (nb067_alpha_dummy_188 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
          ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
          ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0023 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
        ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
        ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
        ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
        ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
        ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
        ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
        ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_181))
              (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb067_alpha_dummy_181)) (Class.cv (nb067_alpha_dummy_177)))
          (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_182 f))
              (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb067_alpha_dummy_182 f))
            (Class.cv (nb067_alpha_dummy_179 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc))))) :=
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
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)),
                          ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)),
                          ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)),
                          ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
                          ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
                          ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
                          ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
                          ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb067_split_alpha_0022 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
              ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
              ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
              ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
              ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
              ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
              ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
              ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
              ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
              ((nb067_alpha_dummy_000), f),
              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)),
              ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)),
              ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)),
              ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)),
              ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
              ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
              ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
              ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
              ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
              ((nb067_alpha_dummy_000), f),
              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))

@[expose]
noncomputable def nb067_split_alpha_0024 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
        ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_199))
          (Class.cab (nb067_alpha_dummy_169)
            (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_199))
            (Class.cab (nb067_alpha_dummy_169)
              (syn_wrex (nb067_alpha_dummy_170) (Class.cv (nb067_alpha_dummy_164))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_169))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_170)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f))
          (Class.cab (nb067_alpha_dummy_171 f)
            (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_200 f))
            (Class.cab (nb067_alpha_dummy_171 f)
              (syn_wrex (nb067_alpha_dummy_172 f) (Class.cv (nb067_alpha_dummy_166 f))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_171 f))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_172 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
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
        (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb067_split_alpha_0023 x y f)))))))
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
        (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb067_split_alpha_0023 x y f)))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                          ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                          ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                          ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                          ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                      (((Class.cv (nb067_alpha_dummy_163))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide))
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
        (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (nb067_split_alpha_0023 x y f)))))))
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
        (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab
        (nb067_split_alpha_0023 x y f)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)),
                            ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)),
                            ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)),
                            ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)),
                            ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)),
                            ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                            ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                            ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                            ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                            ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                            ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                            ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                            ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                            ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                            ((nb067_alpha_dummy_000), f),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
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

@[expose]
noncomputable def nb067_split_alpha_0025 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
        ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
        ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
        ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
        ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_219))
            (syn_cun (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_222 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_223 f))
              (Class.cv (nb067_alpha_dummy_224 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
          ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
          ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
          ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
          ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
          ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
          ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0026 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_214))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_213))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_216 f))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_215 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
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
                          (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
                              ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
                              ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
                              ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                              ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                              ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                              ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                              ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                              ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                              ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                              ((nb067_alpha_dummy_000), f),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067_split_alpha_0025 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                  ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                  ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                  ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                  ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                  ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                  ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                  ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                  ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                  ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                  ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                  ((nb067_alpha_dummy_211), (nb067_alpha_dummy_212 f)),
                  ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                  ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                  ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                  ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb067_split_alpha_0027 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
        ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
        ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
        ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
        ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
        ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_219))
            (syn_cun (Class.cv (nb067_alpha_dummy_220)) (Class.cv (nb067_alpha_dummy_221))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_223 f))
            (Class.cv (nb067_alpha_dummy_224 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_222 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_223 f))
              (Class.cv (nb067_alpha_dummy_224 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
          ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
          ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
          ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
          ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
          ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
          ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
          ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
          ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_213))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_215 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0028 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
        ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
        ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
        ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
        ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
        ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_217))
              (syn_cplc (Class.cv (nb067_alpha_dummy_213)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb067_alpha_dummy_217)) (Class.cv (nb067_alpha_dummy_213)))
          (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_213)) (syn_cnnc)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_218 f))
              (syn_cplc (Class.cv (nb067_alpha_dummy_215 f)) (syn_c1c)))
            (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc)))) (syn_wa
          (Wff.classMem (Class.cv (nb067_alpha_dummy_218 f))
            (Class.cv (nb067_alpha_dummy_215 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_215 f)) (syn_cnnc))))) :=
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
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_221), (nb067_alpha_dummy_224 f)),
                          ((nb067_alpha_dummy_220), (nb067_alpha_dummy_223 f)),
                          ((nb067_alpha_dummy_219), (nb067_alpha_dummy_222 f)),
                          ((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
                          ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
                          ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
                          ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
                          ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                          ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                          ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                          ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                          ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                          ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                          ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                          ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                          ((nb067_alpha_dummy_000), f),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_c1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb067_split_alpha_0027 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
              ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
              ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
              ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
              ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
              ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
              ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
              ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
              ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
              ((nb067_alpha_dummy_000), f),
              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0222) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0223 f) 0))
              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
            [((nb067_alpha_dummy_217), (nb067_alpha_dummy_218 f)),
              ((nb067_alpha_dummy_213), (nb067_alpha_dummy_215 f)),
              ((nb067_alpha_dummy_214), (nb067_alpha_dummy_216 f)),
              ((nb067_alpha_dummy_239), (nb067_alpha_dummy_240 f)),
              ((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
              ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
              ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
              ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
              ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
              ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
              ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
              ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
              ((nb067_alpha_dummy_000), f),
              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))

@[expose]
noncomputable def nb067_split_alpha_0029 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
        ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
        ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
        ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
        ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_206))
            (Class.cv (nb067_alpha_dummy_163))) (Wff.classEq (Class.cv (nb067_alpha_dummy_205))
            (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_206))) (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_208 f))
            (Class.cv (nb067_alpha_dummy_165 f)))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_207 f))
            (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_208 f))) (syn_csn (syn_c0c)))))) :=
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
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv) (by decide))
                    (freshVar_injective (((Class.cv f)).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
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
                                      (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb067_split_alpha_0028 x y f)))))))
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
                                      (((Class.cv (nb067_alpha_dummy_206))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb067_alpha_dummy_208 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb067_split_alpha_0028 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb067_alpha_dummy_237), (nb067_alpha_dummy_238 f)),
                    ((nb067_alpha_dummy_206), (nb067_alpha_dummy_208 f)),
                    ((nb067_alpha_dummy_205), (nb067_alpha_dummy_207 f)),
                    ((nb067_alpha_dummy_235), (nb067_alpha_dummy_236 f)),
                    ((nb067_alpha_dummy_209), (nb067_alpha_dummy_210 f)),
                    ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
                    ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
                    ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
                    ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                    ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                    ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                    ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                    ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                    ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                    ((nb067_alpha_dummy_000), f),
                    ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                    ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                    ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb067_function_occurrence (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Class.cv (nb067_alpha_dummy_000)) (Class.cv f) :=
  by
  have freshness0 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_164) :=
    by
    unfold nb067_alpha_dummy_164
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 1))
  have freshness1 : f ≠ (nb067_alpha_dummy_166 f) :=
    by
    unfold nb067_alpha_dummy_166
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 1))
  have freshness2 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_163) :=
    by
    unfold nb067_alpha_dummy_163
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0262) 0))
  have freshness3 : f ≠ (nb067_alpha_dummy_165 f) :=
    by
    unfold nb067_alpha_dummy_165
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0263 f) 0))
  have freshness4 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_167) :=
    by
    unfold nb067_alpha_dummy_167
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0260) 0))
  have freshness5 : f ≠ (nb067_alpha_dummy_168 f) :=
    by
    unfold nb067_alpha_dummy_168
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0261 f) 0))
  have freshness6 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_085) :=
    by
    unfold nb067_alpha_dummy_085
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))
  have freshness7 : f ≠ (nb067_alpha_dummy_088 f) :=
    by
    unfold nb067_alpha_dummy_088
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))
  have freshness8 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_084) :=
    by
    unfold nb067_alpha_dummy_084
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 1))
  have freshness9 : f ≠ (nb067_alpha_dummy_087 f) :=
    by
    unfold nb067_alpha_dummy_087
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 1))
  have freshness10 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_083) :=
    by
    unfold nb067_alpha_dummy_083
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 0))
  have freshness11 : f ≠ (nb067_alpha_dummy_086 f) :=
    by
    unfold nb067_alpha_dummy_086
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 0))
  have freshness12 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_089) :=
    by
    unfold nb067_alpha_dummy_089
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0257) 0))
  have freshness13 : f ≠ (nb067_alpha_dummy_090 f) :=
    by
    unfold nb067_alpha_dummy_090
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0259 f) 0))
  have freshness14 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_081) :=
    by
    unfold nb067_alpha_dummy_081
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0254) 0))
  have freshness15 : f ≠ (nb067_alpha_dummy_082 f) :=
    by
    unfold nb067_alpha_dummy_082
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0255 f) 0))
  have freshness16 : (nb067_alpha_dummy_000) ≠ (nb067_alpha_dummy_079) :=
    by
    unfold nb067_alpha_dummy_079
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0252) 0))
  have freshness17 : f ≠ (nb067_alpha_dummy_080 f) :=
    by
    unfold nb067_alpha_dummy_080
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

@[expose]
noncomputable def nb067_split_alpha_0030 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)),
        ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classMem
        (syn_cop (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_163)))
        (Class.cv (nb067_alpha_dummy_000)))
      (Wff.classMem (syn_cop (Class.cv (nb067_alpha_dummy_166 f))
          (Class.cv (nb067_alpha_dummy_165 f))) (Class.cv f)) :=
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
                                  (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                                    ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                                    ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 1)) (TAlphaVar.here _ _ _)))))
                                  (nb067_split_alpha_0026 x y f)))))))))
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
                                  (((Class.cv (nb067_alpha_dummy_164))).fv ∪
                                    ((Class.cv (nb067_alpha_dummy_163))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb067_alpha_dummy_166 f))).fv ∪
                                    ((Class.cv (nb067_alpha_dummy_165 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0220) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0221 f) 1)) (TAlphaVar.here _ _ _)))))
                                  (nb067_split_alpha_0026 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb067_split_alpha_0029 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb067_split_alpha_0029 x y f))))))))))))
    (nb067_function_occurrence x y f))

@[expose]
noncomputable def nb067_split_alpha_0031 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)),
        ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.all (nb067_alpha_dummy_164) (Wff.neg (syn_wa
            (Wff.classEq (Class.cv (nb067_alpha_dummy_167))
              (syn_cop (Class.cv (nb067_alpha_dummy_163)) (Class.cv (nb067_alpha_dummy_164))))
            (syn_wbr (Class.cv (nb067_alpha_dummy_164)) (Class.cv (nb067_alpha_dummy_000))
              (Class.cv (nb067_alpha_dummy_163))))))
      (Wff.all (nb067_alpha_dummy_166 f) (Wff.neg (syn_wa
            (Wff.classEq (Class.cv (nb067_alpha_dummy_168 f))
              (syn_cop (Class.cv (nb067_alpha_dummy_165 f))
                (Class.cv (nb067_alpha_dummy_166 f))))
            (syn_wbr (Class.cv (nb067_alpha_dummy_166 f)) (Class.cv f)
              (Class.cv (nb067_alpha_dummy_165 f)))))) :=
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
        (((Class.cv (nb067_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb067_alpha_dummy_163))).fv ∪
        ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 1)) (TAlphaVar.here _ _ _)))))
                                        (nb067_split_alpha_0021 x y f)))))))))
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
        (((Class.cv (nb067_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb067_alpha_dummy_163))).fv ∪
        ((Class.cv (nb067_alpha_dummy_164))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb067_alpha_dummy_165 f))).fv ∪
        ((Class.cv (nb067_alpha_dummy_166 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0182) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0182) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0183 f) 1)) (TAlphaVar.here _ _ _)))))
                                        (nb067_split_alpha_0021 x y f)))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0024 x y f)))))))))
        (nb067_split_alpha_0030 x y f))))

@[expose]
noncomputable def nb067_split_alpha_0032 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
        ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
        ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
        ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
        ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_255))
            (syn_cun (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_258 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_259 f))
              (Class.cv (nb067_alpha_dummy_260 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0282) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0283 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0280) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0281 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
          ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
          ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
          ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
          ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
          ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
          ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
          ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
          ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
          ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0286) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0287 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0284) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0285 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0033 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_249))
          (Class.cv (nb067_alpha_dummy_242))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_250))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_249))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f))
          (Class.cv (nb067_alpha_dummy_244 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_252 f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_251 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0270) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0271 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_242))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_244 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
                                  ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
                                  ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
                                  ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                                  ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                                  ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                                  ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                                  ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                                  ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
                                  ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                                  ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003),
                                    (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0032 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                      ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                      ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                      ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                      ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                      ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
                      ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                      ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                      ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                      ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                      ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                      ((nb067_alpha_dummy_247), (nb067_alpha_dummy_248 f)),
                      ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                      ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                      ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                      ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                      ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                      ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                      ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                      ((nb067_alpha_dummy_000), f),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_split_alpha_0034 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
        ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
        ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
        ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
        ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
        ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_255))
            (syn_cun (Class.cv (nb067_alpha_dummy_256)) (Class.cv (nb067_alpha_dummy_257))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_259 f))
            (Class.cv (nb067_alpha_dummy_260 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_258 f))
            (syn_cun (Class.cv (nb067_alpha_dummy_259 f))
              (Class.cv (nb067_alpha_dummy_260 f)))))) :=
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
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0282) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0283 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0280) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0281 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
          ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
          ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
          ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
          ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
          ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
          ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
          ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
          ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
          ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
          ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
          ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
          ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
          ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
          ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
          ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
          ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
          ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0286) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0287 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0284) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0285 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_249))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_251 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb067_split_alpha_0035 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
        ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
        ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
        ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
        ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
        ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
        ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
        ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
        ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
        ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
        ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
        ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
        ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
        ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
        ((nb067_alpha_dummy_000), f),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_250))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_249)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_249)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_249))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_252 f))
        (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_251 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb067_alpha_dummy_251 f)) (syn_c1c))
          (Class.cv (nb067_alpha_dummy_251 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_242))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb067_alpha_dummy_244 f))).fv) (by decide))
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
                          (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_257), (nb067_alpha_dummy_260 f)),
                              ((nb067_alpha_dummy_256), (nb067_alpha_dummy_259 f)),
                              ((nb067_alpha_dummy_255), (nb067_alpha_dummy_258 f)),
                              ((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                              ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                              ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                              ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
                              ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                              ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                              ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                              ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                              ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                              ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                              ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                              ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                              ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                              ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                              ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                              ((nb067_alpha_dummy_000), f),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb067_split_alpha_0034 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                  ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                  ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                  ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
                  ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                  ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                  ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                  ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                  ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0272) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0273 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb067_alpha_dummy_253), (nb067_alpha_dummy_254 f)),
                  ((nb067_alpha_dummy_249), (nb067_alpha_dummy_251 f)),
                  ((nb067_alpha_dummy_250), (nb067_alpha_dummy_252 f)),
                  ((nb067_alpha_dummy_275), (nb067_alpha_dummy_276 f)),
                  ((nb067_alpha_dummy_273), (nb067_alpha_dummy_274 f)),
                  ((nb067_alpha_dummy_242), (nb067_alpha_dummy_244 f)),
                  ((nb067_alpha_dummy_241), (nb067_alpha_dummy_243 f)),
                  ((nb067_alpha_dummy_271), (nb067_alpha_dummy_272 f)),
                  ((nb067_alpha_dummy_245), (nb067_alpha_dummy_246 f)),
                  ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)),
                  ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)),
                  ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)),
                  ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)),
                  ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)),
                  ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)),
                  ((nb067_alpha_dummy_000), f),
                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
