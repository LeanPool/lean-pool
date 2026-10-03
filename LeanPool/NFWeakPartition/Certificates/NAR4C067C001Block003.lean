/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C067C001Part009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part010`. -/


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
noncomputable def nb067_split_alpha_0000 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)),
        ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)),
        ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)),
        ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
        ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
        ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
        ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
        ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
        ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)),
        ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_029))
            (syn_cun (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_032 x y))
            (syn_cun (Class.cv (nb067_alpha_dummy_033 x y))
              (Class.cv (nb067_alpha_dummy_034 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)),
          ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)),
          ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)),
          ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
          ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
          ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
          ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
          ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
          ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)),
          ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
          ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0001 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
        ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
        ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)),
        ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
        (syn_cphi (Class.cv (nb067_alpha_dummy_016))))
      (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
        (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb067_alpha_dummy_001))).fv ∪ ((Class.cv (nb067_alpha_dummy_002))).fv)
          (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_016))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb067_alpha_dummy_018 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0024) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0025 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0024) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0025 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0022) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb067_alpha_dummy_031),
                                        (nb067_alpha_dummy_034 x y)), ((nb067_alpha_dummy_030),
                                        (nb067_alpha_dummy_033 x y)), ((nb067_alpha_dummy_029),
                                        (nb067_alpha_dummy_032 x y)), ((nb067_alpha_dummy_027),
                                        (nb067_alpha_dummy_028 x y)), ((nb067_alpha_dummy_023),
                                        (nb067_alpha_dummy_025 x y)), ((nb067_alpha_dummy_024),
                                        (nb067_alpha_dummy_026 x y)), ((nb067_alpha_dummy_016),
                                        (nb067_alpha_dummy_018 x y)), ((nb067_alpha_dummy_015),
                                        (nb067_alpha_dummy_017 x y)), ((nb067_alpha_dummy_021),
                                        (nb067_alpha_dummy_022 x y)), ((nb067_alpha_dummy_019),
                                        (nb067_alpha_dummy_020 x y)), ((nb067_alpha_dummy_008),
                                        (nb067_alpha_dummy_010 x y f)),
                                      ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                                      ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                                      ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                                      ((nb067_alpha_dummy_002), y),
                                      ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005),
                                        (nb067_alpha_dummy_006 x y f))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb067_split_alpha_0000 x y f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
                          ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
                          ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
                          ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                          ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                          ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)),
                          ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                          ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
                          ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
                          ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
                          ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                          ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                          ((nb067_alpha_dummy_021), (nb067_alpha_dummy_022 x y)),
                          ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                          ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0002 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)),
        ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)),
        ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)),
        ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
        ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
        ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
        ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)),
        ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
        ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
        ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
        ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
        ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_029))
            (syn_cun (Class.cv (nb067_alpha_dummy_030)) (Class.cv (nb067_alpha_dummy_031))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_033 x y))
            (Class.cv (nb067_alpha_dummy_034 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_032 x y))
            (syn_cun (Class.cv (nb067_alpha_dummy_033 x y))
              (Class.cv (nb067_alpha_dummy_034 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)),
          ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)),
          ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)),
          ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
          ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
          ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
          ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)),
          ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
          ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
          ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
          ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
          ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
          ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_023))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_025 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part011`. -/


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
noncomputable def nb067_split_alpha_0003 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
        ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
        ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)),
        ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
        ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
        ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
        ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
        ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_023))
          (Class.cv (nb067_alpha_dummy_016))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_024))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_023)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_023)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_023))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y))
          (Class.cv (nb067_alpha_dummy_018 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_026 x y))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_025 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_025 x y)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_025 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0020) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0021 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0058) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0059 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0056) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0057 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_016))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_018 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0024) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0025 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0024) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0025 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0022) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb067_alpha_dummy_031), (nb067_alpha_dummy_034 x y)),
                                  ((nb067_alpha_dummy_030), (nb067_alpha_dummy_033 x y)),
                                  ((nb067_alpha_dummy_029), (nb067_alpha_dummy_032 x y)),
                                  ((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
                                  ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
                                  ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
                                  ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)),
                                  ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
                                  ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                                  ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                                  ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
                                  ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                                  ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                                  ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                                  ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                                  ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                                  ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                                  ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                  ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb067_split_alpha_0002 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
                      ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
                      ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
                      ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)),
                      ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
                      ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                      ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                      ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
                      ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                      ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                      ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                      ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                      ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb067_alpha_dummy_027), (nb067_alpha_dummy_028 x y)),
                      ((nb067_alpha_dummy_023), (nb067_alpha_dummy_025 x y)),
                      ((nb067_alpha_dummy_024), (nb067_alpha_dummy_026 x y)),
                      ((nb067_alpha_dummy_049), (nb067_alpha_dummy_050 x y)),
                      ((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
                      ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                      ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                      ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
                      ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                      ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                      ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                      ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                      ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                      ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                      ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                      ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb067_second_coordinate_occurrence (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [(nb067_alpha_dummy_016, (nb067_alpha_dummy_018 x y)),
        (nb067_alpha_dummy_015, (nb067_alpha_dummy_017 x y)),
        ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
        ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Class.cv (nb067_alpha_dummy_002)) (Class.cv y) :=
  by
  have freshness0 : (nb067_alpha_dummy_002) ≠ nb067_alpha_dummy_016 :=
    by
    unfold nb067_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
  have freshness1 : y ≠ (nb067_alpha_dummy_018 x y) :=
    by
    unfold nb067_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
  have freshness2 : (nb067_alpha_dummy_002) ≠ nb067_alpha_dummy_015 :=
    by
    unfold nb067_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  have freshness3 : y ≠ (nb067_alpha_dummy_017 x y) :=
    by
    unfold nb067_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  have freshness4 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_045) :=
    by
    unfold nb067_alpha_dummy_045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0054) 0))
  have freshness5 : y ≠ (nb067_alpha_dummy_046 x y) :=
    by
    unfold nb067_alpha_dummy_046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0055 x y) 0))
  have freshness6 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_019) :=
    by
    unfold nb067_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0051) 0))
  have freshness7 : y ≠ (nb067_alpha_dummy_020 x y) :=
    by
    unfold nb067_alpha_dummy_020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0053 x y) 0))
  have freshness8 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_008) :=
    by
    unfold nb067_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
  have freshness9 : y ≠ (nb067_alpha_dummy_010 x y f) :=
    by
    unfold nb067_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
  have freshness10 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_007) :=
    by
    unfold nb067_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  have freshness11 : y ≠ (nb067_alpha_dummy_009 x y f) :=
    by
    unfold nb067_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  have freshness12 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_013) :=
    by
    unfold nb067_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0048) 0))
  have freshness13 : y ≠ (nb067_alpha_dummy_014 x y f) :=
    by
    unfold nb067_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0049 x y f) 0))
  have freshness14 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_011) :=
    by
    unfold nb067_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0045) 0))
  have freshness15 : y ≠ (nb067_alpha_dummy_012 x y f) :=
    by
    unfold nb067_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0047 x y f) 0))
  have freshness16 : (nb067_alpha_dummy_002) ≠ (nb067_alpha_dummy_003) :=
    by
    unfold nb067_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0))
  have freshness17 : y ≠ (nb067_alpha_dummy_004 x y f) :=
    by
    unfold nb067_alpha_dummy_004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0))
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
noncomputable def nb067_split_alpha_0004 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
        ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_045))
          (Class.cab (nb067_alpha_dummy_015)
            (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb067_alpha_dummy_045))
            (Class.cab (nb067_alpha_dummy_015)
              (syn_wrex (nb067_alpha_dummy_016) (Class.cv (nb067_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_015))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_016)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_046 x y))
          (Class.cab (nb067_alpha_dummy_017 x y)
            (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_046 x y))
            (Class.cab (nb067_alpha_dummy_017 x y)
              (syn_wrex (nb067_alpha_dummy_018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067_alpha_dummy_017 x y))
                  (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_018 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb067_second_coordinate_occurrence x y f)) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_001))).fv ∪
                      ((Class.cv (nb067_alpha_dummy_002))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0003 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb067_split_alpha_0003 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
                          ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                          ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                          ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
                          ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                          ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb067_second_coordinate_occurrence x y f)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb067_alpha_dummy_001))).fv ∪
                        ((Class.cv (nb067_alpha_dummy_002))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0003 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb067_split_alpha_0003 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb067_alpha_dummy_047), (nb067_alpha_dummy_048 x y)),
                            ((nb067_alpha_dummy_016), (nb067_alpha_dummy_018 x y)),
                            ((nb067_alpha_dummy_015), (nb067_alpha_dummy_017 x y)),
                            ((nb067_alpha_dummy_045), (nb067_alpha_dummy_046 x y)),
                            ((nb067_alpha_dummy_019), (nb067_alpha_dummy_020 x y)),
                            ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                            ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                            ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                            ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                            ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                            ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                            ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0005 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)),
        ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)),
        ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)),
        ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
        ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
        ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_057))
            (syn_cun (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_060 x y f))
            (syn_cun (Class.cv (nb067_alpha_dummy_061 x y f))
              (Class.cv (nb067_alpha_dummy_062 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)),
          ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)),
          ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)),
          ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
          ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
          ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
          ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_first_coordinate_occurrence (x : Var) (y : Var) (f : Var)
    (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb067_alpha_dummy_016, (nb067_alpha_dummy_018 x y)),
        (nb067_alpha_dummy_015, (nb067_alpha_dummy_017 x y)),
        (nb067_alpha_dummy_021, (nb067_alpha_dummy_022 x y)),
        (nb067_alpha_dummy_019, (nb067_alpha_dummy_020 x y)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Class.cv (nb067_alpha_dummy_001)) (Class.cv x) :=
  by
  have freshness0 : (nb067_alpha_dummy_001) ≠ nb067_alpha_dummy_016 :=
    by
    unfold nb067_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
  have freshness1 : x ≠ (nb067_alpha_dummy_018 x y) :=
    by
    unfold nb067_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
  have freshness2 : (nb067_alpha_dummy_001) ≠ nb067_alpha_dummy_015 :=
    by
    unfold nb067_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  have freshness3 : x ≠ (nb067_alpha_dummy_017 x y) :=
    by
    unfold nb067_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  have freshness4 : (nb067_alpha_dummy_001) ≠ nb067_alpha_dummy_021 :=
    by
    unfold nb067_alpha_dummy_021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0018) 0))
  have freshness5 : x ≠ (nb067_alpha_dummy_022 x y) :=
    by
    unfold nb067_alpha_dummy_022
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0019 x y) 0))
  have freshness6 : (nb067_alpha_dummy_001) ≠ nb067_alpha_dummy_019 :=
    by
    unfold nb067_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0015) 0))
  have freshness7 : x ≠ (nb067_alpha_dummy_020 x y) :=
    by
    unfold nb067_alpha_dummy_020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0017 x y) 0))
  have freshness8 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_008) :=
    by
    unfold nb067_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
  have freshness9 : x ≠ (nb067_alpha_dummy_010 x y f) :=
    by
    unfold nb067_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
  have freshness10 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_007) :=
    by
    unfold nb067_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  have freshness11 : x ≠ (nb067_alpha_dummy_009 x y f) :=
    by
    unfold nb067_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  have freshness12 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_013) :=
    by
    unfold nb067_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0012) 0))
  have freshness13 : x ≠ (nb067_alpha_dummy_014 x y f) :=
    by
    unfold nb067_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0013 x y f) 0))
  have freshness14 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_011) :=
    by
    unfold nb067_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0009) 0))
  have freshness15 : x ≠ (nb067_alpha_dummy_012 x y f) :=
    by
    unfold nb067_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0011 x y f) 0))
  have freshness16 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_003) :=
    by
    unfold nb067_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0006) 0))
  have freshness17 : x ≠ (nb067_alpha_dummy_004 x y f) :=
    by
    unfold nb067_alpha_dummy_004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0007 x y f) 0))
  have freshness18 : (nb067_alpha_dummy_001) ≠ (nb067_alpha_dummy_002) :=
    by
    unfold nb067_alpha_dummy_001 nb067_alpha_dummy_002
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness19 : x ≠ y := by exact dv_x_y
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15
                        (TAlphaVar.there freshness16 freshness17
                          (TAlphaVar.there freshness18 freshness19
                            (TAlphaVar.here _ _ _))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0006 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_008))
          (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002))))
        (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
            (syn_cphi (Class.cv (nb067_alpha_dummy_008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_010 x y f))
          (syn_cop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
            (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb067_first_coordinate_occurrence x y f dv_x_y))
                            (nb067_split_alpha_0001 x y f)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb067_first_coordinate_occurrence x y f dv_x_y))
                            (nb067_split_alpha_0001 x y f)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0004 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cop (Class.cv (nb067_alpha_dummy_001))
                    (Class.cv (nb067_alpha_dummy_002)))).fv ∪
                ((Class.cv (nb067_alpha_dummy_003))).fv) (by decide)) (freshVar_injective
              (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb067_alpha_dummy_010 x y f))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0064) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb067_support_mem_0065 x y f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0064) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0065 x y f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb067_support_mem_0062) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb067_support_mem_0063 x y f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb067_alpha_dummy_059),
        (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058),
        (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057),
        (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055),
        (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051),
        (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052),
        (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_008),
        (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007),
        (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_013),
        (nb067_alpha_dummy_014 x y f)), ((nb067_alpha_dummy_011),
        (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003),
        (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y),
        ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb067_split_alpha_0005 x y f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
                              ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
                              ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
                              ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                              ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                              ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                              ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
                              ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
                              ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
                              ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                              ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                              ((nb067_alpha_dummy_013), (nb067_alpha_dummy_014 x y f)),
                              ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                              ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                              ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                              ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part012`. -/


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
noncomputable def nb067_split_alpha_0007 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)),
        ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)),
        ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)),
        ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
        ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
        ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
        ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)),
        ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_057))
            (syn_cun (Class.cv (nb067_alpha_dummy_058)) (Class.cv (nb067_alpha_dummy_059))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_061 x y f))
            (Class.cv (nb067_alpha_dummy_062 x y f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb067_alpha_dummy_060 x y f))
            (syn_cun (Class.cv (nb067_alpha_dummy_061 x y f))
              (Class.cv (nb067_alpha_dummy_062 x y f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0069 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0067 x y f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0073 x y f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0071 x y f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb067_alpha_dummy_059), (nb067_alpha_dummy_062 x y f)),
          ((nb067_alpha_dummy_058), (nb067_alpha_dummy_061 x y f)),
          ((nb067_alpha_dummy_057), (nb067_alpha_dummy_060 x y f)),
          ((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
          ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
          ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
          ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)),
          ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)),
          ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
          ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
          ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)),
          ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
          ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
          ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
          ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0077 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0075 x y f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb067_alpha_dummy_053 x y f))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0081 x y f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0079 x y f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb067_split_alpha_0008 (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)),
        ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)),
        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
        ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Class.cab (nb067_alpha_dummy_052)
        (syn_wrex (nb067_alpha_dummy_051) (Class.cv (nb067_alpha_dummy_008))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_052))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_051)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_051)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_051))))))
      (Class.cab (nb067_alpha_dummy_054 x y f)
        (syn_wrex (nb067_alpha_dummy_053 x y f) (Class.cv (nb067_alpha_dummy_010 x y f))
          (Wff.classEq (Class.cv (nb067_alpha_dummy_054 x y f))
            (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb067_alpha_dummy_053 x y f)) (syn_c1c))
              (Class.cv (nb067_alpha_dummy_053 x y f)))))) :=
  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0060) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0061 x y f) 1))
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0090) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0091 x y f) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0089 x y f) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb067_alpha_dummy_008))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb067_alpha_dummy_010 x y f))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0064) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb067_support_mem_0065 x y f) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0064) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb067_support_mem_0065 x y f) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0062) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed [((nb067_alpha_dummy_059),
                                      (nb067_alpha_dummy_062 x y f)), ((nb067_alpha_dummy_058),
                                      (nb067_alpha_dummy_061 x y f)), ((nb067_alpha_dummy_057),
                                      (nb067_alpha_dummy_060 x y f)), ((nb067_alpha_dummy_055),
                                      (nb067_alpha_dummy_056 x y f)), ((nb067_alpha_dummy_051),
                                      (nb067_alpha_dummy_053 x y f)), ((nb067_alpha_dummy_052),
                                      (nb067_alpha_dummy_054 x y f)), ((nb067_alpha_dummy_077),
                                      (nb067_alpha_dummy_078 x y f)), ((nb067_alpha_dummy_075),
                                      (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008),
                                      (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007),
                                      (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073),
                                      (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011),
                                      (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003),
                                      (nb067_alpha_dummy_004 x y f)),
                                    ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                    ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb067_split_alpha_0007 x y f))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
                        ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
                        ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
                        ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)),
                        ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)),
                        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                        ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)),
                        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0063 x y f) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb067_alpha_dummy_055), (nb067_alpha_dummy_056 x y f)),
                        ((nb067_alpha_dummy_051), (nb067_alpha_dummy_053 x y f)),
                        ((nb067_alpha_dummy_052), (nb067_alpha_dummy_054 x y f)),
                        ((nb067_alpha_dummy_077), (nb067_alpha_dummy_078 x y f)),
                        ((nb067_alpha_dummy_075), (nb067_alpha_dummy_076 x y f)),
                        ((nb067_alpha_dummy_008), (nb067_alpha_dummy_010 x y f)),
                        ((nb067_alpha_dummy_007), (nb067_alpha_dummy_009 x y f)),
                        ((nb067_alpha_dummy_073), (nb067_alpha_dummy_074 x y f)),
                        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
                        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
                        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def nb067_function_graph_occurrence (x : Var) (y : Var) (f : Var) :
    TAlphaClass
      [(nb067_alpha_dummy_008, (nb067_alpha_dummy_010 x y f)),
        (nb067_alpha_dummy_007, (nb067_alpha_dummy_009 x y f)),
        (nb067_alpha_dummy_073, (nb067_alpha_dummy_074 x y f)),
        ((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Class.cv (nb067_alpha_dummy_003)) (Class.cv (nb067_alpha_dummy_004 x y f)) :=
  by
  have freshness0 : (nb067_alpha_dummy_003) ≠ nb067_alpha_dummy_008 :=
    by
    unfold nb067_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
  have freshness1 : (nb067_alpha_dummy_004 x y f) ≠ (nb067_alpha_dummy_010 x y f) :=
    by
    unfold nb067_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
  have freshness2 : (nb067_alpha_dummy_003) ≠ nb067_alpha_dummy_007 :=
    by
    unfold nb067_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  have freshness3 : (nb067_alpha_dummy_004 x y f) ≠ (nb067_alpha_dummy_009 x y f) :=
    by
    unfold nb067_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  have freshness4 : (nb067_alpha_dummy_003) ≠ nb067_alpha_dummy_073 :=
    by
    unfold nb067_alpha_dummy_073
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0086) 0))
  have freshness5 : (nb067_alpha_dummy_004 x y f) ≠ (nb067_alpha_dummy_074 x y f) :=
    by
    unfold nb067_alpha_dummy_074
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0087 x y f) 0))
  have freshness6 : (nb067_alpha_dummy_003) ≠ (nb067_alpha_dummy_011) :=
    by
    unfold nb067_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0083) 0))
  have freshness7 : (nb067_alpha_dummy_004 x y f) ≠ (nb067_alpha_dummy_012 x y f) :=
    by
    unfold nb067_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0085 x y f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

@[expose]
noncomputable def nb067_split_alpha_0009 (x : Var) (y : Var) (f : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb067_alpha_dummy_011), (nb067_alpha_dummy_012 x y f)),
        ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)),
        ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
        ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_011)) (syn_ccompl
            (Class.cab (nb067_alpha_dummy_007) (syn_wrex (nb067_alpha_dummy_008)
                (syn_cop (Class.cv (nb067_alpha_dummy_001)) (Class.cv (nb067_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_008)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_011)) (syn_ccompl
              (Class.cab (nb067_alpha_dummy_007)
                (syn_wrex (nb067_alpha_dummy_008) (Class.cv (nb067_alpha_dummy_003))
                  (Wff.classEq (Class.cv (nb067_alpha_dummy_007))
                    (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_008)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb067_alpha_dummy_012 x y f)) (syn_ccompl
            (Class.cab (nb067_alpha_dummy_009 x y f)
              (syn_wrex (nb067_alpha_dummy_010 x y f) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                  (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb067_alpha_dummy_012 x y f)) (syn_ccompl
              (Class.cab (nb067_alpha_dummy_009 x y f) (syn_wrex (nb067_alpha_dummy_010 x y f)
                  (Class.cv (nb067_alpha_dummy_004 x y f))
                  (Wff.classEq (Class.cv (nb067_alpha_dummy_009 x y f))
                    (syn_cun (syn_cphi (Class.cv (nb067_alpha_dummy_010 x y f)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0006 x y f dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb067_split_alpha_0006 x y f dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb067_function_graph_occurrence x y f)) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((syn_cop (Class.cv (nb067_alpha_dummy_001))
                                    (Class.cv (nb067_alpha_dummy_002)))).fv ∪
                                ((Class.cv (nb067_alpha_dummy_003))).fv) (by decide))
                            (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067_split_alpha_0008 x y f)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067_split_alpha_0008 x y f))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed [((nb067_alpha_dummy_075),
                                      (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008),
                                      (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007),
                                      (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073),
                                      (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011),
                                      (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003),
                                      (nb067_alpha_dummy_004 x y f)),
                                    ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                    ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb067_function_graph_occurrence x y f)) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((syn_cop (Class.cv (nb067_alpha_dummy_001))
                                    (Class.cv (nb067_alpha_dummy_002)))).fv ∪
                                ((Class.cv (nb067_alpha_dummy_003))).fv) (by decide))
                            (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb067_alpha_dummy_004 x y f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067_split_alpha_0008 x y f)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb067_split_alpha_0008 x y f))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed [((nb067_alpha_dummy_075),
                                      (nb067_alpha_dummy_076 x y f)), ((nb067_alpha_dummy_008),
                                      (nb067_alpha_dummy_010 x y f)), ((nb067_alpha_dummy_007),
                                      (nb067_alpha_dummy_009 x y f)), ((nb067_alpha_dummy_073),
                                      (nb067_alpha_dummy_074 x y f)), ((nb067_alpha_dummy_011),
                                      (nb067_alpha_dummy_012 x y f)), ((nb067_alpha_dummy_003),
                                      (nb067_alpha_dummy_004 x y f)),
                                    ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x),
                                    ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

theorem nb067_compact_fv_empty_0086 : (nb067_alpha_dummy_081) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0087 (f : Var) :
    (nb067_alpha_dummy_082 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0088 : (nb067_alpha_dummy_079) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0089 (f : Var) :
    (nb067_alpha_dummy_080 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0090 : (nb067_alpha_dummy_000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb067_compact_fv_empty_0091 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
