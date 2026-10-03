/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SecondProjectionAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001048Leaf2ndReflected001. -/


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


namespace SecondProjectionAlpha

@[expose]
noncomputable def split_alpha_0000 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_021, (alpha_dummy_024 x y)), (alpha_dummy_020, (alpha_dummy_023 x y)),
        (alpha_dummy_019, (alpha_dummy_022 x y)),
        (alpha_dummy_017, (alpha_dummy_018 x y)),
        (alpha_dummy_013, (alpha_dummy_015 x y)),
        (alpha_dummy_014, (alpha_dummy_016 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_005, (alpha_dummy_007 x y)),
        (alpha_dummy_011, (alpha_dummy_012 x y)),
        (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y),
        (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_019)
            (syn_cun (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_022 x y))
            (syn_cun (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_021, (alpha_dummy_024 x y)), (alpha_dummy_020, (alpha_dummy_023 x y)),
          (alpha_dummy_019, (alpha_dummy_022 x y)), (alpha_dummy_017, (alpha_dummy_018 x y)),
          (alpha_dummy_013, (alpha_dummy_015 x y)), (alpha_dummy_014, (alpha_dummy_016 x y)),
          (alpha_dummy_006, (alpha_dummy_008 x y)), (alpha_dummy_005, (alpha_dummy_007 x y)),
          (alpha_dummy_011, (alpha_dummy_012 x y)),
          (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y),
          (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
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
                                  (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
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
noncomputable def split_alpha_0001 (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alpha_dummy_006, (alpha_dummy_008 x y)), (alpha_dummy_005, (alpha_dummy_007 x y)),
        (alpha_dummy_011, (alpha_dummy_012 x y)),
        (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y),
        (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_000)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_005) (syn_cphi (Class.cv alpha_dummy_006)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_008 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_007 x y))
            (syn_cphi (Class.cv (alpha_dummy_008 x y)))))) :=
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
              (((Class.cv alpha_dummy_000)).fv ∪ ((Class.cv alpha_dummy_001)).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_006)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_008 x y))).fv) (by decide))
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
                                        [(alpha_dummy_021, (alpha_dummy_024 x y)),
        (alpha_dummy_020, (alpha_dummy_023 x y)), (alpha_dummy_019, (alpha_dummy_022 x y)),
        (alpha_dummy_017, (alpha_dummy_018 x y)), (alpha_dummy_013, (alpha_dummy_015 x y)),
        (alpha_dummy_014, (alpha_dummy_016 x y)), (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_005, (alpha_dummy_007 x y)), (alpha_dummy_011, (alpha_dummy_012 x y)),
        (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0000 x y z))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_017, (alpha_dummy_018 x y)),
                              (alpha_dummy_013, (alpha_dummy_015 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_005, (alpha_dummy_007 x y)),
                              (alpha_dummy_011, (alpha_dummy_012 x y)),
                              (alpha_dummy_009, (alpha_dummy_010 x y)),
                              (alpha_dummy_001, y), (alpha_dummy_000, x),
                              (alpha_dummy_003, (alpha_dummy_004 x y z))]
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
                            [(alpha_dummy_017, (alpha_dummy_018 x y)),
                              (alpha_dummy_013, (alpha_dummy_015 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_005, (alpha_dummy_007 x y)),
                              (alpha_dummy_011, (alpha_dummy_012 x y)),
                              (alpha_dummy_009, (alpha_dummy_010 x y)),
                              (alpha_dummy_001, y), (alpha_dummy_000, x),
                              (alpha_dummy_003, (alpha_dummy_004 x y z))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0002 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_021, (alpha_dummy_024 x y)), (alpha_dummy_020, (alpha_dummy_023 x y)),
        (alpha_dummy_019, (alpha_dummy_022 x y)),
        (alpha_dummy_017, (alpha_dummy_018 x y)),
        (alpha_dummy_013, (alpha_dummy_015 x y)),
        (alpha_dummy_014, (alpha_dummy_016 x y)),
        (alpha_dummy_039, (alpha_dummy_040 x y)),
        (alpha_dummy_037, (alpha_dummy_038 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_005, (alpha_dummy_007 x y)),
        (alpha_dummy_035, (alpha_dummy_036 x y)),
        (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y),
        (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_019)
            (syn_cun (Class.cv alpha_dummy_020) (Class.cv alpha_dummy_021)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_022 x y))
            (syn_cun (Class.cv (alpha_dummy_023 x y)) (Class.cv (alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_021, (alpha_dummy_024 x y)), (alpha_dummy_020, (alpha_dummy_023 x y)),
          (alpha_dummy_019, (alpha_dummy_022 x y)), (alpha_dummy_017, (alpha_dummy_018 x y)),
          (alpha_dummy_013, (alpha_dummy_015 x y)), (alpha_dummy_014, (alpha_dummy_016 x y)),
          (alpha_dummy_039, (alpha_dummy_040 x y)), (alpha_dummy_037, (alpha_dummy_038 x y)),
          (alpha_dummy_006, (alpha_dummy_008 x y)), (alpha_dummy_005, (alpha_dummy_007 x y)),
          (alpha_dummy_035, (alpha_dummy_036 x y)),
          (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y),
          (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
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
                                  (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_013)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv)
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
noncomputable def split_alpha_0003 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_039, (alpha_dummy_040 x y)), (alpha_dummy_037, (alpha_dummy_038 x y)),
        (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_005, (alpha_dummy_007 x y)),
        (alpha_dummy_035, (alpha_dummy_036 x y)),
        (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y),
        (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_039) (syn_cphi (Class.cv alpha_dummy_006)))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_039)
            (syn_cphi (Class.cv alpha_dummy_006)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_040 x y))
          (syn_cphi (Class.cv (alpha_dummy_008 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_040 x y))
            (syn_cphi (Class.cv (alpha_dummy_008 x y)))))) :=
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
                  (freshVar_injective (((Class.cv alpha_dummy_006)).fv) (by decide))
                  (freshVar_injective (((Class.cv (alpha_dummy_008 x y))).fv) (by decide))
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
                                      [(alpha_dummy_021, (alpha_dummy_024 x y)),
                                        (alpha_dummy_020, (alpha_dummy_023 x y)),
                                        (alpha_dummy_019, (alpha_dummy_022 x y)),
                                        (alpha_dummy_017, (alpha_dummy_018 x y)),
                                        (alpha_dummy_013, (alpha_dummy_015 x y)),
                                        (alpha_dummy_014, (alpha_dummy_016 x y)),
                                        (alpha_dummy_039, (alpha_dummy_040 x y)),
                                        (alpha_dummy_037, (alpha_dummy_038 x y)),
                                        (alpha_dummy_006, (alpha_dummy_008 x y)),
                                        (alpha_dummy_005, (alpha_dummy_007 x y)),
                                        (alpha_dummy_035, (alpha_dummy_036 x y)),
                                        (alpha_dummy_009, (alpha_dummy_010 x y)),
                                        (alpha_dummy_001, y), (alpha_dummy_000, x),
                                        (alpha_dummy_003, (alpha_dummy_004 x y z))]
                                      (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (split_alpha_0002 x y z))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [(alpha_dummy_017, (alpha_dummy_018 x y)),
                            (alpha_dummy_013, (alpha_dummy_015 x y)),
                            (alpha_dummy_014, (alpha_dummy_016 x y)),
                            (alpha_dummy_039, (alpha_dummy_040 x y)),
                            (alpha_dummy_037, (alpha_dummy_038 x y)),
                            (alpha_dummy_006, (alpha_dummy_008 x y)),
                            (alpha_dummy_005, (alpha_dummy_007 x y)),
                            (alpha_dummy_035, (alpha_dummy_036 x y)),
                            (alpha_dummy_009, (alpha_dummy_010 x y)),
                            (alpha_dummy_001, y), (alpha_dummy_000, x),
                            (alpha_dummy_003, (alpha_dummy_004 x y z))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [(alpha_dummy_017, (alpha_dummy_018 x y)),
                            (alpha_dummy_013, (alpha_dummy_015 x y)),
                            (alpha_dummy_014, (alpha_dummy_016 x y)),
                            (alpha_dummy_039, (alpha_dummy_040 x y)),
                            (alpha_dummy_037, (alpha_dummy_038 x y)),
                            (alpha_dummy_006, (alpha_dummy_008 x y)),
                            (alpha_dummy_005, (alpha_dummy_007 x y)),
                            (alpha_dummy_035, (alpha_dummy_036 x y)),
                            (alpha_dummy_009, (alpha_dummy_010 x y)),
                            (alpha_dummy_001, y), (alpha_dummy_000, x),
                            (alpha_dummy_003, (alpha_dummy_004 x y z))]
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
                    (freshVar_injective (((Class.cv alpha_dummy_006)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_008 x y))).fv) (by decide))
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
                                        [(alpha_dummy_021, (alpha_dummy_024 x y)),
        (alpha_dummy_020, (alpha_dummy_023 x y)), (alpha_dummy_019, (alpha_dummy_022 x y)),
        (alpha_dummy_017, (alpha_dummy_018 x y)), (alpha_dummy_013, (alpha_dummy_015 x y)),
        (alpha_dummy_014, (alpha_dummy_016 x y)), (alpha_dummy_039, (alpha_dummy_040 x y)),
        (alpha_dummy_037, (alpha_dummy_038 x y)), (alpha_dummy_006, (alpha_dummy_008 x y)),
        (alpha_dummy_005, (alpha_dummy_007 x y)), (alpha_dummy_035, (alpha_dummy_036 x y)),
        (alpha_dummy_009, (alpha_dummy_010 x y)), (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0002 x y z))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_017, (alpha_dummy_018 x y)),
                              (alpha_dummy_013, (alpha_dummy_015 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_039, (alpha_dummy_040 x y)),
                              (alpha_dummy_037, (alpha_dummy_038 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_005, (alpha_dummy_007 x y)),
                              (alpha_dummy_035, (alpha_dummy_036 x y)),
                              (alpha_dummy_009, (alpha_dummy_010 x y)),
                              (alpha_dummy_001, y), (alpha_dummy_000, x),
                              (alpha_dummy_003, (alpha_dummy_004 x y z))]
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
                            [(alpha_dummy_017, (alpha_dummy_018 x y)),
                              (alpha_dummy_013, (alpha_dummy_015 x y)),
                              (alpha_dummy_014, (alpha_dummy_016 x y)),
                              (alpha_dummy_039, (alpha_dummy_040 x y)),
                              (alpha_dummy_037, (alpha_dummy_038 x y)),
                              (alpha_dummy_006, (alpha_dummy_008 x y)),
                              (alpha_dummy_005, (alpha_dummy_007 x y)),
                              (alpha_dummy_035, (alpha_dummy_036 x y)),
                              (alpha_dummy_009, (alpha_dummy_010 x y)),
                              (alpha_dummy_001, y), (alpha_dummy_000, x),
                              (alpha_dummy_003, (alpha_dummy_004 x y z))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0004 (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [(alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.classEq (Class.cv alpha_dummy_003)
        (syn_cop (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))
      (Wff.classEq (Class.cv (alpha_dummy_004 x y z)) (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv
      (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0003 x y z) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0001 x y z) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0001 x y z dv_x_y)))))))))
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
                                  (((Class.cv alpha_dummy_000)).fv ∪
                                    ((Class.cv alpha_dummy_001)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg (split_alpha_0003 x y z)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_037, (alpha_dummy_038 x y)),
                                        (alpha_dummy_006, (alpha_dummy_008 x y)),
                                        (alpha_dummy_005, (alpha_dummy_007 x y)),
                                        (alpha_dummy_035, (alpha_dummy_036 x y)),
                                        (alpha_dummy_009, (alpha_dummy_010 x y)),
                                        (alpha_dummy_001, y), (alpha_dummy_000, x),
                                        (alpha_dummy_003, (alpha_dummy_004 x y z))]
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
                                  (((Class.cv alpha_dummy_000)).fv ∪
                                    ((Class.cv alpha_dummy_001)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg (split_alpha_0003 x y z)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [(alpha_dummy_037, (alpha_dummy_038 x y)),
                                        (alpha_dummy_006, (alpha_dummy_008 x y)),
                                        (alpha_dummy_005, (alpha_dummy_007 x y)),
                                        (alpha_dummy_035, (alpha_dummy_036 x y)),
                                        (alpha_dummy_009, (alpha_dummy_010 x y)),
                                        (alpha_dummy_001, y), (alpha_dummy_000, x),
                                        (alpha_dummy_003, (alpha_dummy_004 x y z))]
                                      (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def split_alpha_0005 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_057, (alpha_dummy_060 y z)), (alpha_dummy_056, (alpha_dummy_059 y z)),
        (alpha_dummy_055, (alpha_dummy_058 y z)),
        (alpha_dummy_053, (alpha_dummy_054 y z)),
        (alpha_dummy_049, (alpha_dummy_051 y z)),
        (alpha_dummy_050, (alpha_dummy_052 y z)),
        (alpha_dummy_042, (alpha_dummy_044 y z)),
        (alpha_dummy_041, (alpha_dummy_043 y z)),
        (alpha_dummy_047, (alpha_dummy_048 y z)),
        (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
        (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_055)
            (syn_cun (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_058 y z))
            (syn_cun (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_057, (alpha_dummy_060 y z)), (alpha_dummy_056, (alpha_dummy_059 y z)),
          (alpha_dummy_055, (alpha_dummy_058 y z)), (alpha_dummy_053, (alpha_dummy_054 y z)),
          (alpha_dummy_049, (alpha_dummy_051 y z)), (alpha_dummy_050, (alpha_dummy_052 y z)),
          (alpha_dummy_042, (alpha_dummy_044 y z)), (alpha_dummy_041, (alpha_dummy_043 y z)),
          (alpha_dummy_047, (alpha_dummy_048 y z)),
          (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
          (alpha_dummy_001, y), (alpha_dummy_000, x),
          (alpha_dummy_003, (alpha_dummy_004 x y z))] (syn_c0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0006 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_042, (alpha_dummy_044 y z)), (alpha_dummy_041, (alpha_dummy_043 y z)),
        (alpha_dummy_047, (alpha_dummy_048 y z)),
        (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
        (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_042) (Class.cv alpha_dummy_002)) (Wff.neg
          (Wff.classEq (Class.cv alpha_dummy_041) (syn_cphi (Class.cv alpha_dummy_042)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_044 y z)) (Class.cv z)) (Wff.neg
          (Wff.classEq (Class.cv (alpha_dummy_043 y z))
            (syn_cphi (Class.cv (alpha_dummy_044 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 1))
          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0044 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0047 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0045 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) (by decide))
            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv alpha_dummy_042)).fv) (by decide))
                    (freshVar_injective (((Class.cv (alpha_dummy_044 y z))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0053 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0051 y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [(alpha_dummy_057, (alpha_dummy_060 y z)),
        (alpha_dummy_056, (alpha_dummy_059 y z)), (alpha_dummy_055, (alpha_dummy_058 y z)),
        (alpha_dummy_053, (alpha_dummy_054 y z)), (alpha_dummy_049, (alpha_dummy_051 y z)),
        (alpha_dummy_050, (alpha_dummy_052 y z)), (alpha_dummy_042, (alpha_dummy_044 y z)),
        (alpha_dummy_041, (alpha_dummy_043 y z)), (alpha_dummy_047, (alpha_dummy_048 y z)),
        (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z), (alpha_dummy_001, y),
        (alpha_dummy_000, x), (alpha_dummy_003, (alpha_dummy_004 x y z))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (split_alpha_0005 x y z))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_053, (alpha_dummy_054 y z)),
                              (alpha_dummy_049, (alpha_dummy_051 y z)),
                              (alpha_dummy_050, (alpha_dummy_052 y z)),
                              (alpha_dummy_042, (alpha_dummy_044 y z)),
                              (alpha_dummy_041, (alpha_dummy_043 y z)),
                              (alpha_dummy_047, (alpha_dummy_048 y z)),
                              (alpha_dummy_045, (alpha_dummy_046 y z)),
                              (alpha_dummy_002, z), (alpha_dummy_001, y), (alpha_dummy_000, x),
                              (alpha_dummy_003, (alpha_dummy_004 x y z))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [(alpha_dummy_053, (alpha_dummy_054 y z)),
                              (alpha_dummy_049, (alpha_dummy_051 y z)),
                              (alpha_dummy_050, (alpha_dummy_052 y z)),
                              (alpha_dummy_042, (alpha_dummy_044 y z)),
                              (alpha_dummy_041, (alpha_dummy_043 y z)),
                              (alpha_dummy_047, (alpha_dummy_048 y z)),
                              (alpha_dummy_045, (alpha_dummy_046 y z)),
                              (alpha_dummy_002, z), (alpha_dummy_001, y), (alpha_dummy_000, x),
                              (alpha_dummy_003, (alpha_dummy_004 x y z))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def split_alpha_0007 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_057, (alpha_dummy_060 y z)), (alpha_dummy_056, (alpha_dummy_059 y z)),
        (alpha_dummy_055, (alpha_dummy_058 y z)),
        (alpha_dummy_053, (alpha_dummy_054 y z)),
        (alpha_dummy_049, (alpha_dummy_051 y z)),
        (alpha_dummy_050, (alpha_dummy_052 y z)),
        (alpha_dummy_075, (alpha_dummy_076 y z)),
        (alpha_dummy_073, (alpha_dummy_074 y z)),
        (alpha_dummy_042, (alpha_dummy_044 y z)),
        (alpha_dummy_041, (alpha_dummy_043 y z)),
        (alpha_dummy_071, (alpha_dummy_072 y z)),
        (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
        (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_055)
            (syn_cun (Class.cv alpha_dummy_056) (Class.cv alpha_dummy_057)))))
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z))) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv (alpha_dummy_058 y z))
            (syn_cun (Class.cv (alpha_dummy_059 y z)) (Class.cv (alpha_dummy_060 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0057 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0055 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) (by decide))
                              (freshVar_injective
                                (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0061 y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [(alpha_dummy_057, (alpha_dummy_060 y z)), (alpha_dummy_056, (alpha_dummy_059 y z)),
          (alpha_dummy_055, (alpha_dummy_058 y z)), (alpha_dummy_053, (alpha_dummy_054 y z)),
          (alpha_dummy_049, (alpha_dummy_051 y z)), (alpha_dummy_050, (alpha_dummy_052 y z)),
          (alpha_dummy_075, (alpha_dummy_076 y z)), (alpha_dummy_073, (alpha_dummy_074 y z)),
          (alpha_dummy_042, (alpha_dummy_044 y z)), (alpha_dummy_041, (alpha_dummy_043 y z)),
          (alpha_dummy_071, (alpha_dummy_072 y z)),
          (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
          (alpha_dummy_001, y), (alpha_dummy_000, x),
          (alpha_dummy_003, (alpha_dummy_004 x y z))] (syn_c0) (by simp only [fv_syn_c0])))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0065 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0062 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0063 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_049)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alpha_dummy_051 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0069 y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0067 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0008 (x : Var) (y : Var) (z : Var) :
    TAlphaWff
      [(alpha_dummy_075, (alpha_dummy_076 y z)), (alpha_dummy_073, (alpha_dummy_074 y z)),
        (alpha_dummy_042, (alpha_dummy_044 y z)),
        (alpha_dummy_041, (alpha_dummy_043 y z)),
        (alpha_dummy_071, (alpha_dummy_072 y z)),
        (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
        (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.classMem (Class.cv alpha_dummy_075) (syn_cphi (Class.cv alpha_dummy_042)))
      (Wff.classMem (Class.cv (alpha_dummy_076 y z))
        (syn_cphi (Class.cv (alpha_dummy_044 y z)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 0))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0049 y z) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 y z) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_042)).fv) (by decide))
                (freshVar_injective (((Class.cv (alpha_dummy_044 y z))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 1))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 y z) 1))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0053 y z) 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [(alpha_dummy_057, (alpha_dummy_060 y z)),
                                      (alpha_dummy_056, (alpha_dummy_059 y z)),
                                      (alpha_dummy_055, (alpha_dummy_058 y z)),
                                      (alpha_dummy_053, (alpha_dummy_054 y z)),
                                      (alpha_dummy_049, (alpha_dummy_051 y z)),
                                      (alpha_dummy_050, (alpha_dummy_052 y z)),
                                      (alpha_dummy_075, (alpha_dummy_076 y z)),
                                      (alpha_dummy_073, (alpha_dummy_074 y z)),
                                      (alpha_dummy_042, (alpha_dummy_044 y z)),
                                      (alpha_dummy_041, (alpha_dummy_043 y z)),
                                      (alpha_dummy_071, (alpha_dummy_072 y z)),
                                      (alpha_dummy_045, (alpha_dummy_046 y z)),
                                      (alpha_dummy_002, z), (alpha_dummy_001, y),
                                      (alpha_dummy_000, x),
                                      (alpha_dummy_003, (alpha_dummy_004 x y z))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (split_alpha_0007 x y z))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [(alpha_dummy_053, (alpha_dummy_054 y z)),
                          (alpha_dummy_049, (alpha_dummy_051 y z)),
                          (alpha_dummy_050, (alpha_dummy_052 y z)),
                          (alpha_dummy_075, (alpha_dummy_076 y z)),
                          (alpha_dummy_073, (alpha_dummy_074 y z)),
                          (alpha_dummy_042, (alpha_dummy_044 y z)),
                          (alpha_dummy_041, (alpha_dummy_043 y z)),
                          (alpha_dummy_071, (alpha_dummy_072 y z)),
                          (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
                          (alpha_dummy_001, y), (alpha_dummy_000, x),
                          (alpha_dummy_003, (alpha_dummy_004 x y z))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0051 y z) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [(alpha_dummy_053, (alpha_dummy_054 y z)),
                          (alpha_dummy_049, (alpha_dummy_051 y z)),
                          (alpha_dummy_050, (alpha_dummy_052 y z)),
                          (alpha_dummy_075, (alpha_dummy_076 y z)),
                          (alpha_dummy_073, (alpha_dummy_074 y z)),
                          (alpha_dummy_042, (alpha_dummy_044 y z)),
                          (alpha_dummy_041, (alpha_dummy_043 y z)),
                          (alpha_dummy_071, (alpha_dummy_072 y z)),
                          (alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
                          (alpha_dummy_001, y), (alpha_dummy_000, x),
                          (alpha_dummy_003, (alpha_dummy_004 x y z))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def split_alpha_0009 (x : Var) (y : Var) (z : Var) (dv_y_z : y ≠ z) :
    TAlphaWff
      [(alpha_dummy_045, (alpha_dummy_046 y z)), (alpha_dummy_002, z),
        (alpha_dummy_001, y), (alpha_dummy_000, x),
        (alpha_dummy_003, (alpha_dummy_004 x y z))]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_045) (syn_ccompl (Class.cab alpha_dummy_041
              (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_002)
                (Wff.classEq (Class.cv alpha_dummy_041)
                  (syn_cphi (Class.cv alpha_dummy_042))))))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_045) (syn_ccompl (Class.cab alpha_dummy_041
                (syn_wrex alpha_dummy_042 (Class.cv alpha_dummy_001)
                  (Wff.classEq (Class.cv alpha_dummy_041)
                    (syn_cun (syn_cphi (Class.cv alpha_dummy_042)) (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_046 y z)) (syn_ccompl
            (Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv z)
                (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                  (syn_cphi (Class.cv (alpha_dummy_044 y z)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_046 y z)) (syn_ccompl
              (Class.cab (alpha_dummy_043 y z) (syn_wrex (alpha_dummy_044 y z) (Class.cv y)
                  (Wff.classEq (Class.cv (alpha_dummy_043 y z))
                    (syn_cun (syn_cphi (Class.cv (alpha_dummy_044 y z)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0006 x y z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (split_alpha_0006 x y z))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 y z) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 y z) 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alpha_dummy_002)).fv ∪
                                ((Class.cv alpha_dummy_001)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (split_alpha_0008 x y z)
                                      (split_alpha_0008 x y z)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [(alpha_dummy_073, (alpha_dummy_074 y z)),
                                    (alpha_dummy_042, (alpha_dummy_044 y z)),
                                    (alpha_dummy_041, (alpha_dummy_043 y z)),
                                    (alpha_dummy_071, (alpha_dummy_072 y z)),
                                    (alpha_dummy_045, (alpha_dummy_046 y z)),
                                    (alpha_dummy_002, z), (alpha_dummy_001, y),
                                    (alpha_dummy_000, x),
                                    (alpha_dummy_003, (alpha_dummy_004 x y z))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 1))
                            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0072 y z) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 y z) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0073 y z) 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv alpha_dummy_002)).fv ∪
                                ((Class.cv alpha_dummy_001)).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (split_alpha_0008 x y z)
                                      (split_alpha_0008 x y z)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [(alpha_dummy_073, (alpha_dummy_074 y z)),
                                    (alpha_dummy_042, (alpha_dummy_044 y z)),
                                    (alpha_dummy_041, (alpha_dummy_043 y z)),
                                    (alpha_dummy_071, (alpha_dummy_072 y z)),
                                    (alpha_dummy_045, (alpha_dummy_046 y z)),
                                    (alpha_dummy_002, z), (alpha_dummy_001, y),
                                    (alpha_dummy_000, x),
                                    (alpha_dummy_003, (alpha_dummy_004 x y z))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

end SecondProjectionAlpha

@[expose]
noncomputable def nominal_df_2nd (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_c2nd)
        (syn_copab x y (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (SecondProjectionAlpha.split_alpha_0004 x y z dv_x_y) (TAlphaWff.ex
                (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.neg
                        (SecondProjectionAlpha.split_alpha_0009 x y z dv_y_z))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
