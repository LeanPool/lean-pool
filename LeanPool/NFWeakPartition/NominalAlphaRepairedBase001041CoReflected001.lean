/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.CompositionAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001041CoReflected001. -/


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


namespace CompositionAlpha

@[expose]
noncomputable def split_alpha_0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
        ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
        ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
        ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
        ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
        ((alpha_dummy_011 A B), (alpha_dummy_012 x y)),
        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_019 A B))
            (syn_cun (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_022 x y))
            (syn_cun (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
          ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
          ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
          ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
          ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
          ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
          ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
          ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
          ((alpha_dummy_011 A B), (alpha_dummy_012 x y)),
          ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
          ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0001 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
        ((alpha_dummy_011 A B), (alpha_dummy_012 x y)),
        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_006 A B)) (Class.cv (alpha_dummy_000 A B)))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_005 A B))
            (syn_cphi (Class.cv (alpha_dummy_006 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_008 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_007 x y))
            (syn_cphi (Class.cv (alpha_dummy_008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0004 A B) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0008 A B) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0005 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_001 A B))).fv)
              (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alpha_dummy_006 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alpha_dummy_008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
        ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
        ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
        ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
        ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
        ((alpha_dummy_011 A B), (alpha_dummy_012 x y)),
        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0000 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                              ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                              ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                              ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                              ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                              ((alpha_dummy_011 A B), (alpha_dummy_012 x y)),
                              ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                              ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                              ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                              ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                              ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                              ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                              ((alpha_dummy_011 A B), (alpha_dummy_012 x y)),
                              ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                              ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0002 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
        ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
        ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
        ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
        ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
        ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
        ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
        ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_019 A B))
            (syn_cun (Class.cv (alpha_dummy_020 A B)) (Class.cv (alpha_dummy_021 A B))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_022 x y))
            (syn_cun (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
          ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
          ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
          ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
          ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
          ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
          ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
          ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
          ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
          ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
          ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
          ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
          ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_013 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
        ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
        ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_039 A B))
          (syn_cphi (Class.cv (alpha_dummy_006 A B)))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_039 A B))
            (syn_cphi (Class.cv (alpha_dummy_006 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_040 x y))
          (syn_cphi (Class.cv (alpha_dummy_008 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_040 x y))
            (syn_cphi (Class.cv (alpha_dummy_008 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (alpha_dummy_006 A B))).fv) (by decide))
                  (freshVar_injective (((Class.cv (alpha_dummy_008 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0014 A B) 1)) (Nat.ne_of_lt
                                      (mem_lt_freshVar (support_mem_0015 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
                                        ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
                                        ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
                                        ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                                        ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                                        ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                                        ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
                                        ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                                        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                                        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                                        ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                                        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                                        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                                        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                      (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (split_alpha_0002 x y z A B))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                            ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                            ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                            ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
                            ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                            ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                            ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                            ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                            ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                            ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                            ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                            ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                            ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                            ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
                            ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                            ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                            ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                            ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                            ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                            ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                            ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0010 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1)) (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0040 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0038 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alpha_dummy_006 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alpha_dummy_008 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0014 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_021 A B), (alpha_dummy_024 x y)),
        ((alpha_dummy_020 A B), (alpha_dummy_023 x y)),
        ((alpha_dummy_019 A B), (alpha_dummy_022 x y)),
        ((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
        ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
        ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
        ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
        ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
        ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)), ((alpha_dummy_001 A B), y),
        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0002 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                              ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                              ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                              ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
                              ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                              ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                              ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                              ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                              ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                              ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0012 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_017 A B), (alpha_dummy_018 x y)),
                              ((alpha_dummy_013 A B), (alpha_dummy_015 x y)),
                              ((alpha_dummy_014 A B), (alpha_dummy_016 x y)),
                              ((alpha_dummy_039 A B), (alpha_dummy_040 x y)),
                              ((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                              ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                              ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                              ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                              ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                              ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.classEq (Class.cv (alpha_dummy_003 A B))
        (syn_cop (Class.cv (alpha_dummy_000 A B)) (Class.cv (alpha_dummy_001 A B))))
      (Wff.classEq (Class.cv (alpha_dummy_004 x y z A B))
        (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv
      (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0002 A B) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z A B) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0000 A B) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z A B) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z A B dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z A B dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0032 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0034 x y) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0036 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_000 A B))).fv ∪
                                    ((Class.cv (alpha_dummy_001 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (split_alpha_0003 x y z A B)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                                        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                                        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                                        ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                                        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                                        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                                        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0032 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0032 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0034 x y) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0036 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0033 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_000 A B))).fv ∪
                                    ((Class.cv (alpha_dummy_001 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (split_alpha_0003 x y z A B)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_037 A B), (alpha_dummy_038 x y)),
                                        ((alpha_dummy_006 A B), (alpha_dummy_008 x y)),
                                        ((alpha_dummy_005 A B), (alpha_dummy_007 x y)),
                                        ((alpha_dummy_035 A B), (alpha_dummy_036 x y)),
                                        ((alpha_dummy_009 A B), (alpha_dummy_010 x y)),
                                        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
                                        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def split_alpha_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_057 A B), (alpha_dummy_060 x z)),
        ((alpha_dummy_056 A B), (alpha_dummy_059 x z)),
        ((alpha_dummy_055 A B), (alpha_dummy_058 x z)),
        ((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
        ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
        ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
        ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
        ((alpha_dummy_047 A B), (alpha_dummy_048 x z)),
        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_055 A B))
            (syn_cun (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_058 x z))
            (syn_cun (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_057 A B), (alpha_dummy_060 x z)),
          ((alpha_dummy_056 A B), (alpha_dummy_059 x z)),
          ((alpha_dummy_055 A B), (alpha_dummy_058 x z)),
          ((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
          ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
          ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
          ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
          ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
          ((alpha_dummy_047 A B), (alpha_dummy_048 x z)),
          ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
          ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0006 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    TAlphaWff
      [((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
        ((alpha_dummy_047 A B), (alpha_dummy_048 x z)),
        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_042 A B)) (Class.cv (alpha_dummy_000 A B)))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_041 A B))
            (syn_cphi (Class.cv (alpha_dummy_042 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_044 x z)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_043 x z))
            (syn_cphi (Class.cv (alpha_dummy_044 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0042 A B) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 x z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0046 A B) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 x z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0043 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0045 x z) 0))
                (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_z
                  (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (alpha_dummy_000 A B))).fv ∪ ((Class.cv (alpha_dummy_002 A B))).fv)
              (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alpha_dummy_042 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alpha_dummy_044 x z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0052 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 x z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0052 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0053 x z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0050 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0051 x z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_057 A B), (alpha_dummy_060 x z)),
        ((alpha_dummy_056 A B), (alpha_dummy_059 x z)),
        ((alpha_dummy_055 A B), (alpha_dummy_058 x z)),
        ((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
        ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
        ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
        ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
        ((alpha_dummy_047 A B), (alpha_dummy_048 x z)),
        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B),
        (alpha_dummy_004 x y z A B))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0005 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
                              ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
                              ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
                              ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                              ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                              ((alpha_dummy_047 A B), (alpha_dummy_048 x z)),
                              ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                              ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                              ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
                              ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
                              ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
                              ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                              ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                              ((alpha_dummy_047 A B), (alpha_dummy_048 x z)),
                              ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                              ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                              ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0007 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_057 A B), (alpha_dummy_060 x z)),
        ((alpha_dummy_056 A B), (alpha_dummy_059 x z)),
        ((alpha_dummy_055 A B), (alpha_dummy_058 x z)),
        ((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
        ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
        ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
        ((alpha_dummy_075 A B), (alpha_dummy_076 x z)),
        ((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
        ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
        ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_055 A B))
            (syn_cun (Class.cv (alpha_dummy_056 A B)) (Class.cv (alpha_dummy_057 A B))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_058 x z))
            (syn_cun (Class.cv (alpha_dummy_059 x z)) (Class.cv (alpha_dummy_060 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0056 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0054 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0060 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0058 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_057 A B), (alpha_dummy_060 x z)),
          ((alpha_dummy_056 A B), (alpha_dummy_059 x z)),
          ((alpha_dummy_055 A B), (alpha_dummy_058 x z)),
          ((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
          ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
          ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
          ((alpha_dummy_075 A B), (alpha_dummy_076 x z)),
          ((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
          ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
          ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
          ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
          ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
          ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0064 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0062 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_049 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0068 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0066 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_075 A B), (alpha_dummy_076 x z)),
        ((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
        ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
        ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.classMem (Class.cv (alpha_dummy_075 A B))
        (syn_cphi (Class.cv (alpha_dummy_042 A B))))
      (Wff.classMem (Class.cv (alpha_dummy_076 x z))
        (syn_cphi (Class.cv (alpha_dummy_044 x z)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0048 A B) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 x z) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 x z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 x z) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (alpha_dummy_042 A B))).fv) (by decide))
                (freshVar_injective (((Class.cv (alpha_dummy_044 x z))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0052 A B) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0053 x z) 1)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0052 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 x z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0050 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((alpha_dummy_057 A B), (alpha_dummy_060 x z)),
                                      ((alpha_dummy_056 A B), (alpha_dummy_059 x z)),
                                      ((alpha_dummy_055 A B), (alpha_dummy_058 x z)),
                                      ((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
                                      ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
                                      ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
                                      ((alpha_dummy_075 A B), (alpha_dummy_076 x z)),
                                      ((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
                                      ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                                      ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                                      ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
                                      ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                                      ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                                      ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B),
                                        (alpha_dummy_004 x y z A B))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (split_alpha_0007 x y z A B))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
                          ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
                          ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
                          ((alpha_dummy_075 A B), (alpha_dummy_076 x z)),
                          ((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
                          ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                          ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                          ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
                          ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                          ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                          ((alpha_dummy_000 A B), x),
                          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0050 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 x z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((alpha_dummy_053 A B), (alpha_dummy_054 x z)),
                          ((alpha_dummy_049 A B), (alpha_dummy_051 x z)),
                          ((alpha_dummy_050 A B), (alpha_dummy_052 x z)),
                          ((alpha_dummy_075 A B), (alpha_dummy_076 x z)),
                          ((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
                          ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                          ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                          ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
                          ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                          ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                          ((alpha_dummy_000 A B), x),
                          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def wpp_refl_0014 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) :
    TReflOn
      [((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (B).fv :=
  by
  intro u hu
  exact
    (TAlphaVar.there (fun h_eq => ((wpp_notmem_0202 A B)) (h_eq ▸ hu))
      (fun h_eq => ((wpp_notmem_0203 z B dv_B_z)) (h_eq ▸ hu))
      (TAlphaVar.there (fun h_eq => ((wpp_notmem_0200 A B)) (h_eq ▸ hu))
        (fun h_eq => ((wpp_notmem_0201 y B dv_B_y)) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => ((wpp_notmem_0198 A B)) (h_eq ▸ hu))
          (fun h_eq => ((wpp_notmem_0199 x B dv_B_x)) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => ((wpp_notmem_0196 A B)) (h_eq ▸ hu))
            (fun h_eq => ((wpp_notmem_0197 x y z A B dv_B_z)) (h_eq ▸ hu))
            (TAlphaVar.free (by simp) (by simp))))))

@[expose]
noncomputable def split_alpha_0009 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) :
    TAlphaWff
      [((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.classMem
        (syn_cop (Class.cv (alpha_dummy_000 A B)) (Class.cv (alpha_dummy_002 A B))) B)
      (Wff.classMem (syn_cop (Class.cv x) (Class.cv z)) B) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (split_alpha_0006 x y z A B dv_x_y dv_x_z)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (split_alpha_0006 x y z A B dv_x_y dv_x_z)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0070 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0072 x z) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 x z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0071 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 x z) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_000 A B))).fv ∪
                                    ((Class.cv (alpha_dummy_002 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (split_alpha_0008 x y z A B)
        (split_alpha_0008 x y z A B))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
                                        ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                                        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                                        ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
                                        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                                        ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                                        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B),
        (alpha_dummy_004 x y z A B))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0070 A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 x z) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0070 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0072 x z) 0)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 x z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0071 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 x z) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_000 A B))).fv ∪
                                    ((Class.cv (alpha_dummy_002 A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (split_alpha_0008 x y z A B)
        (split_alpha_0008 x y z A B))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((alpha_dummy_073 A B), (alpha_dummy_074 x z)),
                                        ((alpha_dummy_042 A B), (alpha_dummy_044 x z)),
                                        ((alpha_dummy_041 A B), (alpha_dummy_043 x z)),
                                        ((alpha_dummy_071 A B), (alpha_dummy_072 x z)),
                                        ((alpha_dummy_045 A B), (alpha_dummy_046 x z)),
                                        ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                                        ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B),
        (alpha_dummy_004 x y z A B))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c]))))))))))))))))))
    (TAlphaClass.refl_of_reflOn
      [((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      B (wpp_refl_0014 x y z A B dv_B_x dv_B_y dv_B_z)))

@[expose]
noncomputable def split_alpha_0010 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_093 A B), (alpha_dummy_096 y z)),
        ((alpha_dummy_092 A B), (alpha_dummy_095 y z)),
        ((alpha_dummy_091 A B), (alpha_dummy_094 y z)),
        ((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
        ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
        ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
        ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
        ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
        ((alpha_dummy_083 A B), (alpha_dummy_084 y z)),
        ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_091 A B))
            (syn_cun (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_094 y z))
            (syn_cun (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_093 A B), (alpha_dummy_096 y z)),
          ((alpha_dummy_092 A B), (alpha_dummy_095 y z)),
          ((alpha_dummy_091 A B), (alpha_dummy_094 y z)),
          ((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
          ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
          ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
          ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
          ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
          ((alpha_dummy_083 A B), (alpha_dummy_084 y z)),
          ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
          ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0011 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
        ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
        ((alpha_dummy_083 A B), (alpha_dummy_084 y z)),
        ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_078 A B)) (Class.cv (alpha_dummy_002 A B)))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_077 A B))
            (syn_cphi (Class.cv (alpha_dummy_078 A B))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_080 y z)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_079 y z))
            (syn_cphi (Class.cv (alpha_dummy_080 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0080 A B) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0084 A B) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0085 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0081 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0083 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (alpha_dummy_002 A B))).fv ∪
                ((Class.cv (alpha_dummy_001 A B))).fv) (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (alpha_dummy_078 A B))).fv)
                      (by decide)) (freshVar_injective (((Class.cv (alpha_dummy_080 y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0090 A B) 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0090 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0091 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0088 A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((alpha_dummy_093 A B), (alpha_dummy_096 y z)),
        ((alpha_dummy_092 A B), (alpha_dummy_095 y z)),
        ((alpha_dummy_091 A B), (alpha_dummy_094 y z)),
        ((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
        ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
        ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
        ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
        ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
        ((alpha_dummy_083 A B), (alpha_dummy_084 y z)),
        ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B),
        (alpha_dummy_004 x y z A B))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0010 x y z A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
                              ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
                              ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
                              ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                              ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                              ((alpha_dummy_083 A B), (alpha_dummy_084 y z)),
                              ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                              ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                              ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
                              ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
                              ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
                              ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                              ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                              ((alpha_dummy_083 A B), (alpha_dummy_084 y z)),
                              ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                              ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                              ((alpha_dummy_000 A B), x),
                              ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0012 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_093 A B), (alpha_dummy_096 y z)),
        ((alpha_dummy_092 A B), (alpha_dummy_095 y z)),
        ((alpha_dummy_091 A B), (alpha_dummy_094 y z)),
        ((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
        ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
        ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
        ((alpha_dummy_111 A B), (alpha_dummy_112 y z)),
        ((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
        ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
        ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
        ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
        ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_091 A B))
            (syn_cun (Class.cv (alpha_dummy_092 A B)) (Class.cv (alpha_dummy_093 A B))))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_094 y z))
            (syn_cun (Class.cv (alpha_dummy_095 y z)) (Class.cv (alpha_dummy_096 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0094 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0092 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0098 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0096 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((alpha_dummy_093 A B), (alpha_dummy_096 y z)),
          ((alpha_dummy_092 A B), (alpha_dummy_095 y z)),
          ((alpha_dummy_091 A B), (alpha_dummy_094 y z)),
          ((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
          ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
          ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
          ((alpha_dummy_111 A B), (alpha_dummy_112 y z)),
          ((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
          ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
          ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
          ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
          ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
          ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0102 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0100 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alpha_dummy_085 A B))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_087 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0106 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0104 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0013 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alpha_dummy_111 A B), (alpha_dummy_112 y z)),
        ((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
        ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
        ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
        ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
        ((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.classMem (Class.cv (alpha_dummy_111 A B))
        (syn_cphi (Class.cv (alpha_dummy_078 A B))))
      (Wff.classMem (Class.cv (alpha_dummy_112 y z))
        (syn_cphi (Class.cv (alpha_dummy_080 y z)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0086 A B) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 y z) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0116 A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0117 y z) 0)) (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0114 A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0115 y z) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (alpha_dummy_078 A B))).fv) (by decide))
                (freshVar_injective (((Class.cv (alpha_dummy_080 y z))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0090 A B) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0091 y z) 1)) (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0090 A B) 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 y z) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (support_mem_0088 A B) 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((alpha_dummy_093 A B), (alpha_dummy_096 y z)),
                                      ((alpha_dummy_092 A B), (alpha_dummy_095 y z)),
                                      ((alpha_dummy_091 A B), (alpha_dummy_094 y z)),
                                      ((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
                                      ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
                                      ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
                                      ((alpha_dummy_111 A B), (alpha_dummy_112 y z)),
                                      ((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
                                      ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                                      ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                                      ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
                                      ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                                      ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                                      ((alpha_dummy_000 A B), x), ((alpha_dummy_003 A B),
                                        (alpha_dummy_004 x y z A B))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (split_alpha_0012 x y z A B))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
                          ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
                          ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
                          ((alpha_dummy_111 A B), (alpha_dummy_112 y z)),
                          ((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
                          ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                          ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                          ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
                          ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                          ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                          ((alpha_dummy_000 A B), x),
                          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0088 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((alpha_dummy_089 A B), (alpha_dummy_090 y z)),
                          ((alpha_dummy_085 A B), (alpha_dummy_087 y z)),
                          ((alpha_dummy_086 A B), (alpha_dummy_088 y z)),
                          ((alpha_dummy_111 A B), (alpha_dummy_112 y z)),
                          ((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
                          ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                          ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                          ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
                          ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                          ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                          ((alpha_dummy_000 A B), x),
                          ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def split_alpha_0014 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((alpha_dummy_081 A B), (alpha_dummy_082 y z)), ((alpha_dummy_002 A B), z),
        ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_081 A B)) (syn_ccompl
            (Class.cab (alpha_dummy_077 A B)
              (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_002 A B))
                (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                  (syn_cphi (Class.cv (alpha_dummy_078 A B)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_081 A B)) (syn_ccompl
              (Class.cab (alpha_dummy_077 A B)
                (syn_wrex (alpha_dummy_078 A B) (Class.cv (alpha_dummy_001 A B))
                  (Wff.classEq (Class.cv (alpha_dummy_077 A B))
                    (syn_cun (syn_cphi (Class.cv (alpha_dummy_078 A B)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_082 y z)) (syn_ccompl
            (Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                  (syn_cphi (Class.cv (alpha_dummy_080 y z)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_082 y z)) (syn_ccompl
              (Class.cab (alpha_dummy_079 y z) (syn_wrex (alpha_dummy_080 y z) (Class.cv y)
                  (Wff.classEq (Class.cv (alpha_dummy_079 y z))
                    (syn_cun (syn_cphi (Class.cv (alpha_dummy_080 y z)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0011 x y z A B)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0011 x y z A B))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0112 A B) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0109 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0111 y z) 0)) (TAlphaVar.there
                                    (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alpha_dummy_002 A B))).fv ∪
                                ((Class.cv (alpha_dummy_001 A B))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (split_alpha_0013 x y z A B)
                                      (split_alpha_0013 x y z A B)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
                                    ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                                    ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                                    ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
                                    ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                                    ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                                    ((alpha_dummy_000 A B), x),
                                    ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0108 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0112 A B) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0109 A B) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (support_mem_0111 y z) 0)) (TAlphaVar.there
                                    (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alpha_dummy_002 A B))).fv ∪
                                ((Class.cv (alpha_dummy_001 A B))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (split_alpha_0013 x y z A B)
                                      (split_alpha_0013 x y z A B)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((alpha_dummy_109 A B), (alpha_dummy_110 y z)),
                                    ((alpha_dummy_078 A B), (alpha_dummy_080 y z)),
                                    ((alpha_dummy_077 A B), (alpha_dummy_079 y z)),
                                    ((alpha_dummy_107 A B), (alpha_dummy_108 y z)),
                                    ((alpha_dummy_081 A B), (alpha_dummy_082 y z)),
                                    ((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y),
                                    ((alpha_dummy_000 A B), x),
                                    ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

@[expose]
noncomputable def wpp_refl_0022 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) :
    TReflOn
      [((alpha_dummy_002 A B), z), ((alpha_dummy_001 A B), y), ((alpha_dummy_000 A B), x),
        ((alpha_dummy_003 A B), (alpha_dummy_004 x y z A B))]
      (A).fv :=
  by
  intro u hu
  exact
    (TAlphaVar.there (fun h_eq => ((wpp_notmem_0292 A B)) (h_eq ▸ hu))
      (fun h_eq => ((wpp_notmem_0293 z A dv_A_z)) (h_eq ▸ hu))
      (TAlphaVar.there (fun h_eq => ((wpp_notmem_0290 A B)) (h_eq ▸ hu))
        (fun h_eq => ((wpp_notmem_0291 y A dv_A_y)) (h_eq ▸ hu))
        (TAlphaVar.there (fun h_eq => ((wpp_notmem_0288 A B)) (h_eq ▸ hu))
          (fun h_eq => ((wpp_notmem_0289 x A dv_A_x)) (h_eq ▸ hu))
          (TAlphaVar.there (fun h_eq => ((wpp_notmem_0286 A B)) (h_eq ▸ hu))
            (fun h_eq => ((wpp_notmem_0287 x y z A B dv_A_z)) (h_eq ▸ hu))
            (TAlphaVar.free (by simp) (by simp))))))

end CompositionAlpha

@[expose]
noncomputable def nominal_df_co (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_ccom A B) (syn_copab x y (syn_wex z
            (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (CompositionAlpha.split_alpha_0004 x y z A B dv_x_y) (TAlphaWff.ex
                (TAlphaWff.conj
                  (CompositionAlpha.split_alpha_0009 x y z A B dv_B_x dv_B_y dv_B_z dv_x_y
                    dv_x_z) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                          (CompositionAlpha.split_alpha_0014 x y z A B dv_y_z))))
                    (TAlphaClass.refl_of_reflOn [((CompositionAlpha.alpha_dummy_002 A B), z),
                        ((CompositionAlpha.alpha_dummy_001 A B), y),
                        ((CompositionAlpha.alpha_dummy_000 A B), x),
                        ((CompositionAlpha.alpha_dummy_003 A B),
                          (CompositionAlpha.alpha_dummy_004 x y z A B))] A
                      (CompositionAlpha.wpp_refl_0022 x y z A B dv_A_x dv_A_y dv_A_z)))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
