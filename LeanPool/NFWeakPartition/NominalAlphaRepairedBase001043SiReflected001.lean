/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SingletonImageAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001043SiReflected001. -/


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

/-! Shared variable, support, and alpha-certificate components. -/


namespace SingletonImageAlpha

@[expose]
noncomputable def split_alpha_0000 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
        ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
        ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
        ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
        ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
        ((alpha_dummy_012 A), (alpha_dummy_013 x y)),
        ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_020 A))
            (syn_cun (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_023 x y))
            (syn_cun (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
          ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
          ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
          ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
          ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
          ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
          ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
          ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
          ((alpha_dummy_012 A), (alpha_dummy_013 x y)),
          ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
          ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0001 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alpha_dummy_007 A), (alpha_dummy_009 x y)),
        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
        ((alpha_dummy_012 A), (alpha_dummy_013 x y)),
        ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_007 A)) (Class.cv (alpha_dummy_001 A)))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_006 A))
            (syn_cphi (Class.cv (alpha_dummy_007 A))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_009 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_008 x y))
            (syn_cphi (Class.cv (alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0008 A) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0005 A) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alpha_dummy_001 A))).fv ∪ ((Class.cv (alpha_dummy_002 A))).fv)
              (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (alpha_dummy_007 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
        ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
        ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
        ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
        ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
        ((alpha_dummy_012 A), (alpha_dummy_013 x y)),
        ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0000 x y z w A))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                              ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                              ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                              ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                              ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                              ((alpha_dummy_012 A), (alpha_dummy_013 x y)),
                              ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                              ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                              ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                              ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                              ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                              ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                              ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                              ((alpha_dummy_012 A), (alpha_dummy_013 x y)),
                              ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                              ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                              ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0002 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
        ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
        ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
        ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
        ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
        ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
        ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
        ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
        ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_020 A))
            (syn_cun (Class.cv (alpha_dummy_021 A)) (Class.cv (alpha_dummy_022 A))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_023 x y))
            (syn_cun (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
          ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
          ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
          ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
          ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
          ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
          ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
          ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
          ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
          ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
          ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
          ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
          ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_014 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0003 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alpha_dummy_040 A), (alpha_dummy_041 x y)),
        ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
        ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
        ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_040 A))
          (syn_cphi (Class.cv (alpha_dummy_007 A)))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_040 A))
            (syn_cphi (Class.cv (alpha_dummy_007 A))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_041 x y))
          (syn_cphi (Class.cv (alpha_dummy_009 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_041 x y))
            (syn_cphi (Class.cv (alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (alpha_dummy_007 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (alpha_dummy_009 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0014 A) 1)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0015 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
                                        ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
                                        ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
                                        ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                                        ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                                        ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                                        ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
                                        ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                                        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                                        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                                        ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                                        ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                                        ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                                        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                      (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (split_alpha_0002 x y z w A))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                            ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                            ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                            ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
                            ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                            ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                            ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                            ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                            ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                            ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                            ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                            ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                            ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                            ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
                            ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                            ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                            ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                            ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                            ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                            ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                            ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (alpha_dummy_007 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_022 A), (alpha_dummy_025 x y)),
        ((alpha_dummy_021 A), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A), (alpha_dummy_023 x y)),
        ((alpha_dummy_018 A), (alpha_dummy_019 x y)),
        ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
        ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
        ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
        ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
        ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
        ((alpha_dummy_010 A), (alpha_dummy_011 x y)), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0002 x y z w A))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                              ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                              ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                              ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
                              ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                              ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                              ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                              ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                              ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                              ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                              ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_018 A), (alpha_dummy_019 x y)),
                              ((alpha_dummy_014 A), (alpha_dummy_016 x y)),
                              ((alpha_dummy_015 A), (alpha_dummy_017 x y)),
                              ((alpha_dummy_040 A), (alpha_dummy_041 x y)),
                              ((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                              ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                              ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                              ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                              ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                              ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                              ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
def swapped_variable (x y z w : Var) (A : Class) :
    TAlphaClass
      [((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), alpha_dummy_005 x y z w A)]
      (Class.cv (alpha_dummy_004 A)) (Class.cv (alpha_dummy_005 x y z w A)) :=
  by
  have leftSecond : (alpha_dummy_002 A) ≠ (alpha_dummy_004 A) :=
    by
    unfold alpha_dummy_004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0002 A) 0)
  have rightSecond : y ≠ alpha_dummy_005 x y z w A :=
    by
    unfold alpha_dummy_005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z w A) 0)
  have leftFirst : (alpha_dummy_001 A) ≠ (alpha_dummy_004 A) :=
    by
    unfold alpha_dummy_004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0000 A) 0)
  have rightFirst : x ≠ alpha_dummy_005 x y z w A :=
    by
    unfold alpha_dummy_005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z w A) 0)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there leftSecond.symm rightSecond.symm
          (TAlphaVar.there leftFirst.symm rightFirst.symm (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def split_alpha_0004 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.classEq (Class.cv (alpha_dummy_004 A))
        (syn_cop (Class.cv (alpha_dummy_001 A)) (Class.cv (alpha_dummy_002 A))))
      (Wff.classEq (Class.cv (alpha_dummy_005 x y z w A))
        (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (swapped_variable x y z w A) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z w A dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z w A dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0036 A) 0)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_001 A))).fv ∪
                                    ((Class.cv (alpha_dummy_002 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (split_alpha_0003 x y z w A)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                                        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                                        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                                        ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                                        ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                                        ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                                        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0036 A) 0)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_001 A))).fv ∪
                                    ((Class.cv (alpha_dummy_002 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (split_alpha_0003 x y z w A)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_038 A), (alpha_dummy_039 x y)),
                                        ((alpha_dummy_007 A), (alpha_dummy_009 x y)),
                                        ((alpha_dummy_006 A), (alpha_dummy_008 x y)),
                                        ((alpha_dummy_036 A), (alpha_dummy_037 x y)),
                                        ((alpha_dummy_010 A), (alpha_dummy_011 x y)),
                                        ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                                        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def split_alpha_0005 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alpha_dummy_062 A), (alpha_dummy_065 z w)),
        ((alpha_dummy_061 A), (alpha_dummy_064 z w)),
        ((alpha_dummy_060 A), (alpha_dummy_063 z w)),
        ((alpha_dummy_058 A), (alpha_dummy_059 z w)),
        ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
        ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
        ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
        ((alpha_dummy_052 A), (alpha_dummy_053 z w)),
        ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
        ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_060 A))
            (syn_cun (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_063 z w))
            (syn_cun (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_062 A), (alpha_dummy_065 z w)),
          ((alpha_dummy_061 A), (alpha_dummy_064 z w)),
          ((alpha_dummy_060 A), (alpha_dummy_063 z w)),
          ((alpha_dummy_058 A), (alpha_dummy_059 z w)),
          ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
          ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
          ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
          ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
          ((alpha_dummy_052 A), (alpha_dummy_053 z w)),
          ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
          ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
          ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0006 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [((alpha_dummy_047 A), (alpha_dummy_049 z w)),
        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
        ((alpha_dummy_052 A), (alpha_dummy_053 z w)),
        ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
        ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_047 A)) (Class.cv (alpha_dummy_003 A)))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_046 A))
            (syn_cphi (Class.cv (alpha_dummy_047 A))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_049 z w)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_048 z w))
            (syn_cphi (Class.cv (alpha_dummy_049 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 z w) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 A) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                  (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alpha_dummy_003 A))).fv ∪ ((Class.cv (alpha_dummy_000 A))).fv)
              (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (alpha_dummy_047 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_049 z w))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0056 A) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0057 z w) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0056 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0057 z w) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0054 A) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0055 z w) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_062 A), (alpha_dummy_065 z w)),
        ((alpha_dummy_061 A), (alpha_dummy_064 z w)),
        ((alpha_dummy_060 A), (alpha_dummy_063 z w)),
        ((alpha_dummy_058 A), (alpha_dummy_059 z w)),
        ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
        ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
        ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
        ((alpha_dummy_052 A), (alpha_dummy_053 z w)),
        ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
        ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0005 x y z w A))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_058 A), (alpha_dummy_059 z w)),
                              ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
                              ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
                              ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                              ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                              ((alpha_dummy_052 A), (alpha_dummy_053 z w)),
                              ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                              ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                              ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                              ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_058 A), (alpha_dummy_059 z w)),
                              ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
                              ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
                              ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                              ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                              ((alpha_dummy_052 A), (alpha_dummy_053 z w)),
                              ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                              ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                              ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                              ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0007 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alpha_dummy_062 A), (alpha_dummy_065 z w)),
        ((alpha_dummy_061 A), (alpha_dummy_064 z w)),
        ((alpha_dummy_060 A), (alpha_dummy_063 z w)),
        ((alpha_dummy_058 A), (alpha_dummy_059 z w)),
        ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
        ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
        ((alpha_dummy_080 A), (alpha_dummy_081 z w)),
        ((alpha_dummy_078 A), (alpha_dummy_079 z w)),
        ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
        ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
        ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
        ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_060 A))
            (syn_cun (Class.cv (alpha_dummy_061 A)) (Class.cv (alpha_dummy_062 A))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_063 z w))
            (syn_cun (Class.cv (alpha_dummy_064 z w)) (Class.cv (alpha_dummy_065 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_062 A), (alpha_dummy_065 z w)),
          ((alpha_dummy_061 A), (alpha_dummy_064 z w)),
          ((alpha_dummy_060 A), (alpha_dummy_063 z w)),
          ((alpha_dummy_058 A), (alpha_dummy_059 z w)),
          ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
          ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
          ((alpha_dummy_080 A), (alpha_dummy_081 z w)),
          ((alpha_dummy_078 A), (alpha_dummy_079 z w)),
          ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
          ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
          ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
          ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
          ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
          ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_054 A))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_056 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 A) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0071 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0008 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class) :
    TAlphaWff
      [((alpha_dummy_055 A), (alpha_dummy_057 z w)),
        ((alpha_dummy_080 A), (alpha_dummy_081 z w)),
        ((alpha_dummy_078 A), (alpha_dummy_079 z w)),
        ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
        ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
        ((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
        ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.all (alpha_dummy_054 A) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (alpha_dummy_054 A)) (Class.cv (alpha_dummy_047 A)))
            (Wff.classEq (Class.cv (alpha_dummy_055 A))
              (syn_cif (Wff.classMem (Class.cv (alpha_dummy_054 A)) (syn_cnnc))
                (syn_cplc (Class.cv (alpha_dummy_054 A)) (syn_c1c))
                (Class.cv (alpha_dummy_054 A)))))))
      (Wff.all (alpha_dummy_056 z w) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (alpha_dummy_056 z w)) (Class.cv (alpha_dummy_049 z w)))
            (Wff.classEq (Class.cv (alpha_dummy_057 z w))
              (syn_cif (Wff.classMem (Class.cv (alpha_dummy_056 z w)) (syn_cnnc))
                (syn_cplc (Class.cv (alpha_dummy_056 z w)) (syn_c1c))
                (Class.cv (alpha_dummy_056 z w))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 A) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0083 z w) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0081 z w) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_047 A))).fv) (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_049 z w))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0054 A) 0)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0055 z w) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((alpha_dummy_062 A), (alpha_dummy_065 z w)),
                                    ((alpha_dummy_061 A), (alpha_dummy_064 z w)),
                                    ((alpha_dummy_060 A), (alpha_dummy_063 z w)),
                                    ((alpha_dummy_058 A), (alpha_dummy_059 z w)),
                                    ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
                                    ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
                                    ((alpha_dummy_080 A), (alpha_dummy_081 z w)),
                                    ((alpha_dummy_078 A), (alpha_dummy_079 z w)),
                                    ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                                    ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                                    ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
                                    ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                                    ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                                    ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                                    ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (split_alpha_0007 x y z w A))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((alpha_dummy_058 A), (alpha_dummy_059 z w)),
                        ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
                        ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
                        ((alpha_dummy_080 A), (alpha_dummy_081 z w)),
                        ((alpha_dummy_078 A), (alpha_dummy_079 z w)),
                        ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                        ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
                        ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                        ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                        ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((alpha_dummy_058 A), (alpha_dummy_059 z w)),
                        ((alpha_dummy_054 A), (alpha_dummy_056 z w)),
                        ((alpha_dummy_055 A), (alpha_dummy_057 z w)),
                        ((alpha_dummy_080 A), (alpha_dummy_081 z w)),
                        ((alpha_dummy_078 A), (alpha_dummy_079 z w)),
                        ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                        ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                        ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
                        ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                        ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                        ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def split_alpha_0009 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [((alpha_dummy_050 A), (alpha_dummy_051 z w)), ((alpha_dummy_000 A), w),
        ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
        ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_050 A)) (syn_ccompl
            (Class.cab (alpha_dummy_046 A)
              (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_003 A))
                (Wff.classEq (Class.cv (alpha_dummy_046 A))
                  (syn_cphi (Class.cv (alpha_dummy_047 A)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_050 A)) (syn_ccompl
              (Class.cab (alpha_dummy_046 A)
                (syn_wrex (alpha_dummy_047 A) (Class.cv (alpha_dummy_000 A))
                  (Wff.classEq (Class.cv (alpha_dummy_046 A))
                    (syn_cun (syn_cphi (Class.cv (alpha_dummy_047 A)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_051 z w)) (syn_ccompl
            (Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                  (syn_cphi (Class.cv (alpha_dummy_049 z w)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_051 z w)) (syn_ccompl
              (Class.cab (alpha_dummy_048 z w) (syn_wrex (alpha_dummy_049 z w) (Class.cv w)
                  (Wff.classEq (Class.cv (alpha_dummy_048 z w))
                    (syn_cun (syn_cphi (Class.cv (alpha_dummy_049 z w)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0006 x y z w A dv_w_z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0006 x y z w A dv_w_z)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alpha_dummy_003 A))).fv ∪
                                ((Class.cv (alpha_dummy_000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w A)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w A))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((alpha_dummy_078 A), (alpha_dummy_079 z w)),
                                    ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                                    ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                                    ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
                                    ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                                    ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                                    ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                                    ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alpha_dummy_003 A))).fv ∪
                                ((Class.cv (alpha_dummy_000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w A)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w A))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((alpha_dummy_078 A), (alpha_dummy_079 z w)),
                                    ((alpha_dummy_047 A), (alpha_dummy_049 z w)),
                                    ((alpha_dummy_046 A), (alpha_dummy_048 z w)),
                                    ((alpha_dummy_076 A), (alpha_dummy_077 z w)),
                                    ((alpha_dummy_050 A), (alpha_dummy_051 z w)),
                                    ((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z),
                                    ((alpha_dummy_002 A), y), ((alpha_dummy_001 A), x),
                                    ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

@[expose]
noncomputable def wpp_refl_0014 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) :
    TReflOn
      [((alpha_dummy_000 A), w), ((alpha_dummy_003 A), z), ((alpha_dummy_002 A), y),
        ((alpha_dummy_001 A), x), ((alpha_dummy_004 A), (alpha_dummy_005 x y z w A))]
      (A).fv :=
  by
  intro u hu
  exact
    (TAlphaVar.there (fun h_eq => ((wpp_notmem_0212 A)) (h_eq ▸ hu))
      (fun h_eq => ((wpp_notmem_0213 w A dv_A_w)) (h_eq ▸ hu))
      (TAlphaVar.there (fun h_eq => ((wpp_notmem_0210 A)) (h_eq ▸ hu))
        (fun h_eq => ((wpp_notmem_0211 z A dv_A_z)) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => ((wpp_notmem_0208 A)) (h_eq ▸ hu))
          (fun h_eq => ((wpp_notmem_0209 y A dv_A_y)) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => ((wpp_notmem_0206 A)) (h_eq ▸ hu))
            (fun h_eq => ((wpp_notmem_0207 x A dv_A_x)) (h_eq ▸ hu))
            (TAlphaVar.there (fun h_eq => ((wpp_notmem_0204 A)) (h_eq ▸ hu))
              (fun h_eq => ((wpp_notmem_0205 x y z w A dv_A_w dv_A_z)) (h_eq ▸ hu))
              (TAlphaVar.free (by simp) (by simp)))))))

end SingletonImageAlpha

@[expose]
noncomputable def nominal_df_si (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_csi A) (syn_copab x y (syn_wex z (syn_wex w
              (syn_w3a (.classEq (.cv x) (syn_csn (.cv z)))
                (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) A (.cv w))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (SingletonImageAlpha.split_alpha_0004 x y z w A dv_x_y)
              (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classEq
                        (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                            (Ne.symm dv_w_x)
                            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_z
                              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                dv_x_y (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
                                    (SingletonImageAlpha.support_mem_0042 A) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (SingletonImageAlpha.support_mem_0043 z) 0))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                            (Ne.symm dv_w_y)
                            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                              dv_y_z (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
                                    (SingletonImageAlpha.support_mem_0044 A) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (SingletonImageAlpha.support_mem_0045 w) 0))
                                (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                            (SingletonImageAlpha.split_alpha_0009 x y z w A dv_w_z))))
                      (TAlphaClass.refl_of_reflOn [((SingletonImageAlpha.alpha_dummy_000 A), w),
                          ((SingletonImageAlpha.alpha_dummy_003 A), z),
                          ((SingletonImageAlpha.alpha_dummy_002 A), y),
                          ((SingletonImageAlpha.alpha_dummy_001 A), x),
                          ((SingletonImageAlpha.alpha_dummy_004 A),
                            (SingletonImageAlpha.alpha_dummy_005 x y z w A))] A
                        (SingletonImageAlpha.wpp_refl_0014 x y z w A dv_A_w dv_A_x dv_A_y
                          dv_A_z))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
