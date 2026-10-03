/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SwapAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001039SwapReflected001. -/


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

/-! Shared variable, support, and alpha-certificate components for swap. -/


namespace SwapAlpha

@[expose]
noncomputable def split_alpha_0000 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_022, (alpha_dummy_025 x y)), (alpha_dummy_021, (alpha_dummy_024 x y)),
        (alpha_dummy_020, (alpha_dummy_023 x y)),
        (alpha_dummy_018, (alpha_dummy_019 x y)),
        (alpha_dummy_014, (alpha_dummy_016 x y)),
        (alpha_dummy_015, (alpha_dummy_017 x y)),
        (alpha_dummy_007, (alpha_dummy_009 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_012, (alpha_dummy_013 x y)),
        (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y),
        (alpha_dummy_001, x), (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_020)
            (syn_cun (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_023 x y))
            (syn_cun (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_022, (alpha_dummy_025 x y)), (alpha_dummy_021, (alpha_dummy_024 x y)),
          (alpha_dummy_020, (alpha_dummy_023 x y)), (alpha_dummy_018, (alpha_dummy_019 x y)),
          (alpha_dummy_014, (alpha_dummy_016 x y)), (alpha_dummy_015, (alpha_dummy_017 x y)),
          (alpha_dummy_007, (alpha_dummy_009 x y)), (alpha_dummy_006, (alpha_dummy_008 x y)),
          (alpha_dummy_012, (alpha_dummy_013 x y)),
          (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y),
          (alpha_dummy_001, x), (alpha_dummy_004, (alpha_dummy_005 x y z w))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0001 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alpha_dummy_007, (alpha_dummy_009 x y)), (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_012, (alpha_dummy_013 x y)),
        (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y),
        (alpha_dummy_001, x), (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_007) (Class.cv alpha_dummy_001)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_006) (syn_cphi (Class.cv alpha_dummy_007)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_009 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_008 x y))
            (syn_cphi (Class.cv (alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_022, (alpha_dummy_025 x y)),
        (alpha_dummy_021, (alpha_dummy_024 x y)), (alpha_dummy_020, (alpha_dummy_023 x y)),
        (alpha_dummy_018, (alpha_dummy_019 x y)), (alpha_dummy_014, (alpha_dummy_016 x y)),
        (alpha_dummy_015, (alpha_dummy_017 x y)), (alpha_dummy_007, (alpha_dummy_009 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)), (alpha_dummy_012, (alpha_dummy_013 x y)),
        (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0000 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_018, (alpha_dummy_019 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_015, (alpha_dummy_017 x y)),
                              (alpha_dummy_007, (alpha_dummy_009 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_012, (alpha_dummy_013 x y)),
                              (alpha_dummy_010, (alpha_dummy_011 x y)),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_018, (alpha_dummy_019 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_015, (alpha_dummy_017 x y)),
                              (alpha_dummy_007, (alpha_dummy_009 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_012, (alpha_dummy_013 x y)),
                              (alpha_dummy_010, (alpha_dummy_011 x y)),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0002 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_022, (alpha_dummy_025 x y)), (alpha_dummy_021, (alpha_dummy_024 x y)),
        (alpha_dummy_020, (alpha_dummy_023 x y)),
        (alpha_dummy_018, (alpha_dummy_019 x y)),
        (alpha_dummy_014, (alpha_dummy_016 x y)),
        (alpha_dummy_015, (alpha_dummy_017 x y)),
        (alpha_dummy_040, (alpha_dummy_041 x y)),
        (alpha_dummy_038, (alpha_dummy_039 x y)),
        (alpha_dummy_007, (alpha_dummy_009 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_036, (alpha_dummy_037 x y)),
        (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y),
        (alpha_dummy_001, x), (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_020)
            (syn_cun (Class.cv alpha_dummy_021) (Class.cv alpha_dummy_022)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_023 x y))
            (syn_cun (Class.cv (alpha_dummy_024 x y)) (Class.cv (alpha_dummy_025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_022, (alpha_dummy_025 x y)), (alpha_dummy_021, (alpha_dummy_024 x y)),
          (alpha_dummy_020, (alpha_dummy_023 x y)), (alpha_dummy_018, (alpha_dummy_019 x y)),
          (alpha_dummy_014, (alpha_dummy_016 x y)), (alpha_dummy_015, (alpha_dummy_017 x y)),
          (alpha_dummy_040, (alpha_dummy_041 x y)), (alpha_dummy_038, (alpha_dummy_039 x y)),
          (alpha_dummy_007, (alpha_dummy_009 x y)), (alpha_dummy_006, (alpha_dummy_008 x y)),
          (alpha_dummy_036, (alpha_dummy_037 x y)),
          (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y),
          (alpha_dummy_001, x), (alpha_dummy_004, (alpha_dummy_005 x y z w))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_016 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0003 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_040, (alpha_dummy_041 x y)), (alpha_dummy_038, (alpha_dummy_039 x y)),
        (alpha_dummy_007, (alpha_dummy_009 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_036, (alpha_dummy_037 x y)),
        (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y),
        (alpha_dummy_001, x), (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_040) (syn_cphi (Class.cv alpha_dummy_007)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_040)
            (syn_cphi (Class.cv alpha_dummy_007)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_041 x y))
          (syn_cphi (Class.cv (alpha_dummy_009 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_041 x y))
            (syn_cphi (Class.cv (alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide))
                  (freshVar_injective (((Class.cv (alpha_dummy_009 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_022, (alpha_dummy_025 x y)),
                                        (alpha_dummy_021, (alpha_dummy_024 x y)),
                                        (alpha_dummy_020, (alpha_dummy_023 x y)),
                                        (alpha_dummy_018, (alpha_dummy_019 x y)),
                                        (alpha_dummy_014, (alpha_dummy_016 x y)),
                                        (alpha_dummy_015, (alpha_dummy_017 x y)),
                                        (alpha_dummy_040, (alpha_dummy_041 x y)),
                                        (alpha_dummy_038, (alpha_dummy_039 x y)),
                                        (alpha_dummy_007, (alpha_dummy_009 x y)),
                                        (alpha_dummy_006, (alpha_dummy_008 x y)),
                                        (alpha_dummy_036, (alpha_dummy_037 x y)),
                                        (alpha_dummy_010, (alpha_dummy_011 x y)),
                                        (alpha_dummy_002, y), (alpha_dummy_001, x),
                                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                      (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (split_alpha_0002 x y z w))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [(alpha_dummy_018, (alpha_dummy_019 x y)),
                            (alpha_dummy_014, (alpha_dummy_016 x y)),
                            (alpha_dummy_015, (alpha_dummy_017 x y)),
                            (alpha_dummy_040, (alpha_dummy_041 x y)),
                            (alpha_dummy_038, (alpha_dummy_039 x y)),
                            (alpha_dummy_007, (alpha_dummy_009 x y)),
                            (alpha_dummy_006, (alpha_dummy_008 x y)),
                            (alpha_dummy_036, (alpha_dummy_037 x y)),
                            (alpha_dummy_010, (alpha_dummy_011 x y)),
                            (alpha_dummy_002, y), (alpha_dummy_001, x),
                            (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [(alpha_dummy_018, (alpha_dummy_019 x y)),
                            (alpha_dummy_014, (alpha_dummy_016 x y)),
                            (alpha_dummy_015, (alpha_dummy_017 x y)),
                            (alpha_dummy_040, (alpha_dummy_041 x y)),
                            (alpha_dummy_038, (alpha_dummy_039 x y)),
                            (alpha_dummy_007, (alpha_dummy_009 x y)),
                            (alpha_dummy_006, (alpha_dummy_008 x y)),
                            (alpha_dummy_036, (alpha_dummy_037 x y)),
                            (alpha_dummy_010, (alpha_dummy_011 x y)),
                            (alpha_dummy_002, y), (alpha_dummy_001, x),
                            (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0041 x y) 0))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_007)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_009 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_022, (alpha_dummy_025 x y)),
        (alpha_dummy_021, (alpha_dummy_024 x y)), (alpha_dummy_020, (alpha_dummy_023 x y)),
        (alpha_dummy_018, (alpha_dummy_019 x y)), (alpha_dummy_014, (alpha_dummy_016 x y)),
        (alpha_dummy_015, (alpha_dummy_017 x y)), (alpha_dummy_040, (alpha_dummy_041 x y)),
        (alpha_dummy_038, (alpha_dummy_039 x y)), (alpha_dummy_007, (alpha_dummy_009 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)), (alpha_dummy_036, (alpha_dummy_037 x y)),
        (alpha_dummy_010, (alpha_dummy_011 x y)), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0002 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_018, (alpha_dummy_019 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_015, (alpha_dummy_017 x y)),
                              (alpha_dummy_040, (alpha_dummy_041 x y)),
                              (alpha_dummy_038, (alpha_dummy_039 x y)),
                              (alpha_dummy_007, (alpha_dummy_009 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_036, (alpha_dummy_037 x y)),
                              (alpha_dummy_010, (alpha_dummy_011 x y)),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_018, (alpha_dummy_019 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_015, (alpha_dummy_017 x y)),
                              (alpha_dummy_040, (alpha_dummy_041 x y)),
                              (alpha_dummy_038, (alpha_dummy_039 x y)),
                              (alpha_dummy_007, (alpha_dummy_009 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_036, (alpha_dummy_037 x y)),
                              (alpha_dummy_010, (alpha_dummy_011 x y)),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
def swapped_variable (x y z w : Var) :
    TAlphaClass
      [(alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, alpha_dummy_005 x y z w)]
      (Class.cv alpha_dummy_004) (Class.cv (alpha_dummy_005 x y z w)) :=
  by
  have leftSecond : alpha_dummy_002 ≠ alpha_dummy_004 :=
    by
    unfold alpha_dummy_004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)
  have rightSecond : y ≠ alpha_dummy_005 x y z w :=
    by
    unfold alpha_dummy_005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z w) 0)
  have leftFirst : alpha_dummy_001 ≠ alpha_dummy_004 :=
    by
    unfold alpha_dummy_004
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)
  have rightFirst : x ≠ alpha_dummy_005 x y z w :=
    by
    unfold alpha_dummy_005
    with_reducible exact Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z w) 0)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there leftSecond.symm rightSecond.symm
          (TAlphaVar.there leftFirst.symm rightFirst.symm (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def split_alpha_0004 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.classEq (Class.cv alpha_dummy_004)
        (syn_cop (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))
      (Wff.classEq (Class.cv (alpha_dummy_005 x y z w)) (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (swapped_variable x y z w) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z w dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z w dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪
                                    ((Class.cv alpha_dummy_002)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (split_alpha_0003 x y z w)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_038, (alpha_dummy_039 x y)),
                                        (alpha_dummy_007, (alpha_dummy_009 x y)),
                                        (alpha_dummy_006, (alpha_dummy_008 x y)),
                                        (alpha_dummy_036, (alpha_dummy_037 x y)),
                                        (alpha_dummy_010, (alpha_dummy_011 x y)),
                                        (alpha_dummy_002, y), (alpha_dummy_001, x),
                                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0034 x y) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0037 x y) 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪
                                    ((Class.cv alpha_dummy_002)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (split_alpha_0003 x y z w)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_038, (alpha_dummy_039 x y)),
                                        (alpha_dummy_007, (alpha_dummy_009 x y)),
                                        (alpha_dummy_006, (alpha_dummy_008 x y)),
                                        (alpha_dummy_036, (alpha_dummy_037 x y)),
                                        (alpha_dummy_010, (alpha_dummy_011 x y)),
                                        (alpha_dummy_002, y), (alpha_dummy_001, x),
                                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def split_alpha_0005 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_058, (alpha_dummy_061 z w)), (alpha_dummy_057, (alpha_dummy_060 z w)),
        (alpha_dummy_056, (alpha_dummy_059 z w)),
        (alpha_dummy_054, (alpha_dummy_055 z w)),
        (alpha_dummy_050, (alpha_dummy_052 z w)),
        (alpha_dummy_051, (alpha_dummy_053 z w)),
        (alpha_dummy_043, (alpha_dummy_045 z w)),
        (alpha_dummy_042, (alpha_dummy_044 z w)),
        (alpha_dummy_048, (alpha_dummy_049 z w)),
        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_056)
            (syn_cun (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_059 z w))
            (syn_cun (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_058, (alpha_dummy_061 z w)), (alpha_dummy_057, (alpha_dummy_060 z w)),
          (alpha_dummy_056, (alpha_dummy_059 z w)), (alpha_dummy_054, (alpha_dummy_055 z w)),
          (alpha_dummy_050, (alpha_dummy_052 z w)), (alpha_dummy_051, (alpha_dummy_053 z w)),
          (alpha_dummy_043, (alpha_dummy_045 z w)), (alpha_dummy_042, (alpha_dummy_044 z w)),
          (alpha_dummy_048, (alpha_dummy_049 z w)),
          (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
          (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
          (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0006 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [(alpha_dummy_043, (alpha_dummy_045 z w)), (alpha_dummy_042, (alpha_dummy_044 z w)),
        (alpha_dummy_048, (alpha_dummy_049 z w)),
        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_003)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_042) (syn_cphi (Class.cv alpha_dummy_043)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_045 z w)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_044 z w))
            (syn_cphi (Class.cv (alpha_dummy_045 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 z w) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0045 z w) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_w_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv alpha_dummy_003)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_045 z w))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0053 z w) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0051 z w) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_058, (alpha_dummy_061 z w)),
        (alpha_dummy_057, (alpha_dummy_060 z w)), (alpha_dummy_056, (alpha_dummy_059 z w)),
        (alpha_dummy_054, (alpha_dummy_055 z w)), (alpha_dummy_050, (alpha_dummy_052 z w)),
        (alpha_dummy_051, (alpha_dummy_053 z w)), (alpha_dummy_043, (alpha_dummy_045 z w)),
        (alpha_dummy_042, (alpha_dummy_044 z w)), (alpha_dummy_048, (alpha_dummy_049 z w)),
        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w), (alpha_dummy_003, z),
        (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0005 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_054, (alpha_dummy_055 z w)),
                              (alpha_dummy_050, (alpha_dummy_052 z w)),
                              (alpha_dummy_051, (alpha_dummy_053 z w)),
                              (alpha_dummy_043, (alpha_dummy_045 z w)),
                              (alpha_dummy_042, (alpha_dummy_044 z w)),
                              (alpha_dummy_048, (alpha_dummy_049 z w)),
                              (alpha_dummy_046, (alpha_dummy_047 z w)),
                              (alpha_dummy_000, w), (alpha_dummy_003, z),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_054, (alpha_dummy_055 z w)),
                              (alpha_dummy_050, (alpha_dummy_052 z w)),
                              (alpha_dummy_051, (alpha_dummy_053 z w)),
                              (alpha_dummy_043, (alpha_dummy_045 z w)),
                              (alpha_dummy_042, (alpha_dummy_044 z w)),
                              (alpha_dummy_048, (alpha_dummy_049 z w)),
                              (alpha_dummy_046, (alpha_dummy_047 z w)),
                              (alpha_dummy_000, w), (alpha_dummy_003, z),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0007 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_058, (alpha_dummy_061 z w)), (alpha_dummy_057, (alpha_dummy_060 z w)),
        (alpha_dummy_056, (alpha_dummy_059 z w)),
        (alpha_dummy_054, (alpha_dummy_055 z w)),
        (alpha_dummy_050, (alpha_dummy_052 z w)),
        (alpha_dummy_051, (alpha_dummy_053 z w)),
        (alpha_dummy_076, (alpha_dummy_077 z w)),
        (alpha_dummy_074, (alpha_dummy_075 z w)),
        (alpha_dummy_043, (alpha_dummy_045 z w)),
        (alpha_dummy_042, (alpha_dummy_044 z w)),
        (alpha_dummy_072, (alpha_dummy_073 z w)),
        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_056)
            (syn_cun (Class.cv alpha_dummy_057) (Class.cv alpha_dummy_058)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_059 z w))
            (syn_cun (Class.cv (alpha_dummy_060 z w)) (Class.cv (alpha_dummy_061 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_058, (alpha_dummy_061 z w)), (alpha_dummy_057, (alpha_dummy_060 z w)),
          (alpha_dummy_056, (alpha_dummy_059 z w)), (alpha_dummy_054, (alpha_dummy_055 z w)),
          (alpha_dummy_050, (alpha_dummy_052 z w)), (alpha_dummy_051, (alpha_dummy_053 z w)),
          (alpha_dummy_076, (alpha_dummy_077 z w)), (alpha_dummy_074, (alpha_dummy_075 z w)),
          (alpha_dummy_043, (alpha_dummy_045 z w)), (alpha_dummy_042, (alpha_dummy_044 z w)),
          (alpha_dummy_072, (alpha_dummy_073 z w)),
          (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
          (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
          (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_050)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_052 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0008 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_051, (alpha_dummy_053 z w)), (alpha_dummy_076, (alpha_dummy_077 z w)),
        (alpha_dummy_074, (alpha_dummy_075 z w)),
        (alpha_dummy_043, (alpha_dummy_045 z w)),
        (alpha_dummy_042, (alpha_dummy_044 z w)),
        (alpha_dummy_072, (alpha_dummy_073 z w)),
        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.all alpha_dummy_050 (Wff.neg
          (syn_wa (Wff.classMem (Class.cv alpha_dummy_050) (Class.cv alpha_dummy_043))
            (Wff.classEq (Class.cv alpha_dummy_051)
              (syn_cif (Wff.classMem (Class.cv alpha_dummy_050) (syn_cnnc))
                (syn_cplc (Class.cv alpha_dummy_050) (syn_c1c)) (Class.cv alpha_dummy_050))))))
      (Wff.all (alpha_dummy_052 z w) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (alpha_dummy_052 z w)) (Class.cv (alpha_dummy_045 z w)))
            (Wff.classEq (Class.cv (alpha_dummy_053 z w))
              (syn_cif (Wff.classMem (Class.cv (alpha_dummy_052 z w)) (syn_cnnc))
                (syn_cplc (Class.cv (alpha_dummy_052 z w)) (syn_c1c))
                (Class.cv (alpha_dummy_052 z w))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 z w) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_043)).fv) (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_045 z w))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 z w) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [(alpha_dummy_058, (alpha_dummy_061 z w)),
                                    (alpha_dummy_057, (alpha_dummy_060 z w)),
                                    (alpha_dummy_056, (alpha_dummy_059 z w)),
                                    (alpha_dummy_054, (alpha_dummy_055 z w)),
                                    (alpha_dummy_050, (alpha_dummy_052 z w)),
                                    (alpha_dummy_051, (alpha_dummy_053 z w)),
                                    (alpha_dummy_076, (alpha_dummy_077 z w)),
                                    (alpha_dummy_074, (alpha_dummy_075 z w)),
                                    (alpha_dummy_043, (alpha_dummy_045 z w)),
                                    (alpha_dummy_042, (alpha_dummy_044 z w)),
                                    (alpha_dummy_072, (alpha_dummy_073 z w)),
                                    (alpha_dummy_046, (alpha_dummy_047 z w)),
                                    (alpha_dummy_000, w), (alpha_dummy_003, z),
                                    (alpha_dummy_002, y), (alpha_dummy_001, x),
                                    (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (split_alpha_0007 x y z w))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [(alpha_dummy_054, (alpha_dummy_055 z w)),
                        (alpha_dummy_050, (alpha_dummy_052 z w)),
                        (alpha_dummy_051, (alpha_dummy_053 z w)),
                        (alpha_dummy_076, (alpha_dummy_077 z w)),
                        (alpha_dummy_074, (alpha_dummy_075 z w)),
                        (alpha_dummy_043, (alpha_dummy_045 z w)),
                        (alpha_dummy_042, (alpha_dummy_044 z w)),
                        (alpha_dummy_072, (alpha_dummy_073 z w)),
                        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
                        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [(alpha_dummy_054, (alpha_dummy_055 z w)),
                        (alpha_dummy_050, (alpha_dummy_052 z w)),
                        (alpha_dummy_051, (alpha_dummy_053 z w)),
                        (alpha_dummy_076, (alpha_dummy_077 z w)),
                        (alpha_dummy_074, (alpha_dummy_075 z w)),
                        (alpha_dummy_043, (alpha_dummy_045 z w)),
                        (alpha_dummy_042, (alpha_dummy_044 z w)),
                        (alpha_dummy_072, (alpha_dummy_073 z w)),
                        (alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
                        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def split_alpha_0009 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [(alpha_dummy_046, (alpha_dummy_047 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_046) (syn_ccompl (Class.cab alpha_dummy_042
              (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_003)
                (Wff.classEq (Class.cv alpha_dummy_042)
                  (syn_cphi (Class.cv alpha_dummy_043))))))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_046) (syn_ccompl (Class.cab alpha_dummy_042
                (syn_wrex alpha_dummy_043 (Class.cv alpha_dummy_000)
                  (Wff.classEq (Class.cv alpha_dummy_042)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_043)) (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_047 z w)) (syn_ccompl
            (Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                  (syn_cphi (Class.cv (alpha_dummy_045 z w)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_047 z w)) (syn_ccompl
              (Class.cab (alpha_dummy_044 z w) (syn_wrex (alpha_dummy_045 z w) (Class.cv w)
                  (Wff.classEq (Class.cv (alpha_dummy_044 z w))
                    (syn_cun (syn_cphi (Class.cv (alpha_dummy_045 z w)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0006 x y z w dv_w_z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0006 x y z w dv_w_z)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alpha_dummy_003)).fv ∪
                                ((Class.cv alpha_dummy_000)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [(alpha_dummy_074, (alpha_dummy_075 z w)),
                                    (alpha_dummy_043, (alpha_dummy_045 z w)),
                                    (alpha_dummy_042, (alpha_dummy_044 z w)),
                                    (alpha_dummy_072, (alpha_dummy_073 z w)),
                                    (alpha_dummy_046, (alpha_dummy_047 z w)),
                                    (alpha_dummy_000, w), (alpha_dummy_003, z),
                                    (alpha_dummy_002, y), (alpha_dummy_001, x),
                                    (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alpha_dummy_003)).fv ∪
                                ((Class.cv alpha_dummy_000)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (split_alpha_0008 x y z w))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [(alpha_dummy_074, (alpha_dummy_075 z w)),
                                    (alpha_dummy_043, (alpha_dummy_045 z w)),
                                    (alpha_dummy_042, (alpha_dummy_044 z w)),
                                    (alpha_dummy_072, (alpha_dummy_073 z w)),
                                    (alpha_dummy_046, (alpha_dummy_047 z w)),
                                    (alpha_dummy_000, w), (alpha_dummy_003, z),
                                    (alpha_dummy_002, y), (alpha_dummy_001, x),
                                    (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

@[expose]
noncomputable def split_alpha_0010 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_094, (alpha_dummy_097 z w)), (alpha_dummy_093, (alpha_dummy_096 z w)),
        (alpha_dummy_092, (alpha_dummy_095 z w)),
        (alpha_dummy_090, (alpha_dummy_091 z w)),
        (alpha_dummy_086, (alpha_dummy_088 z w)),
        (alpha_dummy_087, (alpha_dummy_089 z w)),
        (alpha_dummy_079, (alpha_dummy_081 z w)),
        (alpha_dummy_078, (alpha_dummy_080 z w)),
        (alpha_dummy_084, (alpha_dummy_085 z w)),
        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_092)
            (syn_cun (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_095 z w))
            (syn_cun (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_094, (alpha_dummy_097 z w)), (alpha_dummy_093, (alpha_dummy_096 z w)),
          (alpha_dummy_092, (alpha_dummy_095 z w)), (alpha_dummy_090, (alpha_dummy_091 z w)),
          (alpha_dummy_086, (alpha_dummy_088 z w)), (alpha_dummy_087, (alpha_dummy_089 z w)),
          (alpha_dummy_079, (alpha_dummy_081 z w)), (alpha_dummy_078, (alpha_dummy_080 z w)),
          (alpha_dummy_084, (alpha_dummy_085 z w)),
          (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
          (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
          (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0011 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_079, (alpha_dummy_081 z w)), (alpha_dummy_078, (alpha_dummy_080 z w)),
        (alpha_dummy_084, (alpha_dummy_085 z w)),
        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_079) (Class.cv alpha_dummy_000)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_078) (syn_cphi (Class.cv alpha_dummy_079)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_081 z w)) (Class.cv w)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_080 z w))
            (syn_cphi (Class.cv (alpha_dummy_081 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0080 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0082 z w) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0084 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0085 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0081 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0083 z w) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv) (by decide))
            (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_079)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_081 z w))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 z w) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0090 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0091 z w) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0088 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0089 z w) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_094, (alpha_dummy_097 z w)),
        (alpha_dummy_093, (alpha_dummy_096 z w)), (alpha_dummy_092, (alpha_dummy_095 z w)),
        (alpha_dummy_090, (alpha_dummy_091 z w)), (alpha_dummy_086, (alpha_dummy_088 z w)),
        (alpha_dummy_087, (alpha_dummy_089 z w)), (alpha_dummy_079, (alpha_dummy_081 z w)),
        (alpha_dummy_078, (alpha_dummy_080 z w)), (alpha_dummy_084, (alpha_dummy_085 z w)),
        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w), (alpha_dummy_003, z),
        (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0010 x y z w))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_090, (alpha_dummy_091 z w)),
                              (alpha_dummy_086, (alpha_dummy_088 z w)),
                              (alpha_dummy_087, (alpha_dummy_089 z w)),
                              (alpha_dummy_079, (alpha_dummy_081 z w)),
                              (alpha_dummy_078, (alpha_dummy_080 z w)),
                              (alpha_dummy_084, (alpha_dummy_085 z w)),
                              (alpha_dummy_082, (alpha_dummy_083 z w)),
                              (alpha_dummy_000, w), (alpha_dummy_003, z),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_090, (alpha_dummy_091 z w)),
                              (alpha_dummy_086, (alpha_dummy_088 z w)),
                              (alpha_dummy_087, (alpha_dummy_089 z w)),
                              (alpha_dummy_079, (alpha_dummy_081 z w)),
                              (alpha_dummy_078, (alpha_dummy_080 z w)),
                              (alpha_dummy_084, (alpha_dummy_085 z w)),
                              (alpha_dummy_082, (alpha_dummy_083 z w)),
                              (alpha_dummy_000, w), (alpha_dummy_003, z),
                              (alpha_dummy_002, y), (alpha_dummy_001, x),
                              (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0012 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_094, (alpha_dummy_097 z w)), (alpha_dummy_093, (alpha_dummy_096 z w)),
        (alpha_dummy_092, (alpha_dummy_095 z w)),
        (alpha_dummy_090, (alpha_dummy_091 z w)),
        (alpha_dummy_086, (alpha_dummy_088 z w)),
        (alpha_dummy_087, (alpha_dummy_089 z w)),
        (alpha_dummy_112, (alpha_dummy_113 z w)),
        (alpha_dummy_110, (alpha_dummy_111 z w)),
        (alpha_dummy_079, (alpha_dummy_081 z w)),
        (alpha_dummy_078, (alpha_dummy_080 z w)),
        (alpha_dummy_108, (alpha_dummy_109 z w)),
        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_092)
            (syn_cun (Class.cv alpha_dummy_093) (Class.cv alpha_dummy_094)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_095 z w))
            (syn_cun (Class.cv (alpha_dummy_096 z w)) (Class.cv (alpha_dummy_097 z w)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0094 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0095 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0092 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0093 z w) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0098 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0099 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0096 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0097 z w) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_094, (alpha_dummy_097 z w)), (alpha_dummy_093, (alpha_dummy_096 z w)),
          (alpha_dummy_092, (alpha_dummy_095 z w)), (alpha_dummy_090, (alpha_dummy_091 z w)),
          (alpha_dummy_086, (alpha_dummy_088 z w)), (alpha_dummy_087, (alpha_dummy_089 z w)),
          (alpha_dummy_112, (alpha_dummy_113 z w)), (alpha_dummy_110, (alpha_dummy_111 z w)),
          (alpha_dummy_079, (alpha_dummy_081 z w)), (alpha_dummy_078, (alpha_dummy_080 z w)),
          (alpha_dummy_108, (alpha_dummy_109 z w)),
          (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
          (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
          (alpha_dummy_004, (alpha_dummy_005 x y z w))] (syn_c0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0102 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0103 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0100 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0101 z w) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_086)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_088 z w))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0106 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0107 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0104 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0105 z w) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0013 (x : Var) (y : Var) (z : Var) (w : Var) :
    TAlphaWff
      [(alpha_dummy_087, (alpha_dummy_089 z w)), (alpha_dummy_112, (alpha_dummy_113 z w)),
        (alpha_dummy_110, (alpha_dummy_111 z w)),
        (alpha_dummy_079, (alpha_dummy_081 z w)),
        (alpha_dummy_078, (alpha_dummy_080 z w)),
        (alpha_dummy_108, (alpha_dummy_109 z w)),
        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.all alpha_dummy_086 (Wff.neg
          (syn_wa (Wff.classMem (Class.cv alpha_dummy_086) (Class.cv alpha_dummy_079))
            (Wff.classEq (Class.cv alpha_dummy_087)
              (syn_cif (Wff.classMem (Class.cv alpha_dummy_086) (syn_cnnc))
                (syn_cplc (Class.cv alpha_dummy_086) (syn_c1c)) (Class.cv alpha_dummy_086))))))
      (Wff.all (alpha_dummy_088 z w) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (alpha_dummy_088 z w)) (Class.cv (alpha_dummy_081 z w)))
            (Wff.classEq (Class.cv (alpha_dummy_089 z w))
              (syn_cif (Wff.classMem (Class.cv (alpha_dummy_088 z w)) (syn_cnnc))
                (syn_cplc (Class.cv (alpha_dummy_088 z w)) (syn_c1c))
                (Class.cv (alpha_dummy_088 z w))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0086 1))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0087 z w) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0116 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0117 z w) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0114 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0115 z w) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_079)).fv) (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_081 z w))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 z w) 1))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0090 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0091 z w) 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [(alpha_dummy_094, (alpha_dummy_097 z w)),
                                    (alpha_dummy_093, (alpha_dummy_096 z w)),
                                    (alpha_dummy_092, (alpha_dummy_095 z w)),
                                    (alpha_dummy_090, (alpha_dummy_091 z w)),
                                    (alpha_dummy_086, (alpha_dummy_088 z w)),
                                    (alpha_dummy_087, (alpha_dummy_089 z w)),
                                    (alpha_dummy_112, (alpha_dummy_113 z w)),
                                    (alpha_dummy_110, (alpha_dummy_111 z w)),
                                    (alpha_dummy_079, (alpha_dummy_081 z w)),
                                    (alpha_dummy_078, (alpha_dummy_080 z w)),
                                    (alpha_dummy_108, (alpha_dummy_109 z w)),
                                    (alpha_dummy_082, (alpha_dummy_083 z w)),
                                    (alpha_dummy_000, w), (alpha_dummy_003, z),
                                    (alpha_dummy_002, y), (alpha_dummy_001, x),
                                    (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (split_alpha_0012 x y z w))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [(alpha_dummy_090, (alpha_dummy_091 z w)),
                        (alpha_dummy_086, (alpha_dummy_088 z w)),
                        (alpha_dummy_087, (alpha_dummy_089 z w)),
                        (alpha_dummy_112, (alpha_dummy_113 z w)),
                        (alpha_dummy_110, (alpha_dummy_111 z w)),
                        (alpha_dummy_079, (alpha_dummy_081 z w)),
                        (alpha_dummy_078, (alpha_dummy_080 z w)),
                        (alpha_dummy_108, (alpha_dummy_109 z w)),
                        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
                        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0088 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0089 z w) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [(alpha_dummy_090, (alpha_dummy_091 z w)),
                        (alpha_dummy_086, (alpha_dummy_088 z w)),
                        (alpha_dummy_087, (alpha_dummy_089 z w)),
                        (alpha_dummy_112, (alpha_dummy_113 z w)),
                        (alpha_dummy_110, (alpha_dummy_111 z w)),
                        (alpha_dummy_079, (alpha_dummy_081 z w)),
                        (alpha_dummy_078, (alpha_dummy_080 z w)),
                        (alpha_dummy_108, (alpha_dummy_109 z w)),
                        (alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
                        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
                        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def split_alpha_0014 (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [(alpha_dummy_082, (alpha_dummy_083 z w)), (alpha_dummy_000, w),
        (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x),
        (alpha_dummy_004, (alpha_dummy_005 x y z w))]
      (Wff.classMem (Class.cv alpha_dummy_082) (syn_ccompl (Class.cab alpha_dummy_078
            (syn_wrex alpha_dummy_079 (Class.cv alpha_dummy_003)
              (Wff.classEq (Class.cv alpha_dummy_078)
                (syn_cun (syn_cphi (Class.cv alpha_dummy_079)) (syn_csn (syn_c0c))))))))
      (Wff.classMem (Class.cv (alpha_dummy_083 z w)) (syn_ccompl
          (Class.cab (alpha_dummy_080 z w) (syn_wrex (alpha_dummy_081 z w) (Class.cv z)
              (Wff.classEq (Class.cv (alpha_dummy_080 z w))
                (syn_cun (syn_cphi (Class.cv (alpha_dummy_081 z w)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 1))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0112 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0109 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0111 z w) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_w_z) (TAlphaVar.here _ _ _))))))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (split_alpha_0013 x y z w))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab
                                      (TAlphaWff.neg (split_alpha_0013 x y z w))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [(alpha_dummy_110, (alpha_dummy_111 z w)),
                                (alpha_dummy_079, (alpha_dummy_081 z w)),
                                (alpha_dummy_078, (alpha_dummy_080 z w)),
                                (alpha_dummy_108, (alpha_dummy_109 z w)),
                                (alpha_dummy_082, (alpha_dummy_083 z w)),
                                (alpha_dummy_000, w), (alpha_dummy_003, z),
                                (alpha_dummy_002, y), (alpha_dummy_001, x),
                                (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                              (syn_ccompl (syn_csn (syn_c0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 1))
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0108 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0110 z w) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0112 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0113 z w) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0109 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0111 z w) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_w_z) (TAlphaVar.here _ _ _))))))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_003)).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv w)).fv ∪ ((Class.cv z)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (split_alpha_0013 x y z w))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab
                                      (TAlphaWff.neg (split_alpha_0013 x y z w))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [(alpha_dummy_110, (alpha_dummy_111 z w)),
                                (alpha_dummy_079, (alpha_dummy_081 z w)),
                                (alpha_dummy_078, (alpha_dummy_080 z w)),
                                (alpha_dummy_108, (alpha_dummy_109 z w)),
                                (alpha_dummy_082, (alpha_dummy_083 z w)),
                                (alpha_dummy_000, w), (alpha_dummy_003, z),
                                (alpha_dummy_002, y), (alpha_dummy_001, x),
                                (alpha_dummy_004, (alpha_dummy_005 x y z w))]
                              (syn_ccompl (syn_csn (syn_c0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))))))

end SwapAlpha

@[expose]
noncomputable def nominal_df_swap (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cswap) (syn_copab x y (syn_wex z (syn_wex w
              (syn_wa (.classEq (.cv x) (syn_cop (.cv z) (.cv w)))
                (.classEq (.cv y) (syn_cop (.cv w) (.cv z)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (SwapAlpha.split_alpha_0004 x y z w dv_x_y) (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_w_x) (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                              (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.neg (SwapAlpha.split_alpha_0009 x y z w dv_w_z)))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_y)
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (SwapAlpha.split_alpha_0011 x y z w))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.neg
        (SwapAlpha.split_alpha_0011 x y z w)))))))))
                            (SwapAlpha.split_alpha_0014 x y z w dv_w_z))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
