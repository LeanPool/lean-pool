/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C055C001Part005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C055C001Part006`. -/


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
noncomputable def nb055_split_alpha_0000 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)),
        ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)),
        ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)),
        ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
        ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
        ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)),
        ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_028))
            (syn_cun (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_031 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_032 x y))
              (Class.cv (nb055_alpha_dummy_033 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)),
          ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)),
          ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)),
          ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
          ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
          ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)),
          ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
          ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0001 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)),
        ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
        (syn_cphi (Class.cv (nb055_alpha_dummy_015))))
      (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
        (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
          (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_015))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0024) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0025 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0024) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0025 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0022) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb055_alpha_dummy_030),
                                        (nb055_alpha_dummy_033 x y)), ((nb055_alpha_dummy_029),
                                        (nb055_alpha_dummy_032 x y)), ((nb055_alpha_dummy_028),
                                        (nb055_alpha_dummy_031 x y)), ((nb055_alpha_dummy_026),
                                        (nb055_alpha_dummy_027 x y)), ((nb055_alpha_dummy_022),
                                        (nb055_alpha_dummy_024 x y)), ((nb055_alpha_dummy_023),
                                        (nb055_alpha_dummy_025 x y)), ((nb055_alpha_dummy_015),
                                        (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014),
                                        (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_020),
                                        (nb055_alpha_dummy_021 x y)), ((nb055_alpha_dummy_018),
                                        (nb055_alpha_dummy_019 x y)), ((nb055_alpha_dummy_007),
                                        (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006),
                                        (nb055_alpha_dummy_008 x y)), ((nb055_alpha_dummy_012),
                                        (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010),
                                        (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002),
                                        (nb055_alpha_dummy_003 x y)),
                                      ((nb055_alpha_dummy_001), y),
                                      ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004),
                                        (nb055_alpha_dummy_005 x y))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055_split_alpha_0000 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
                          ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
                          ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)),
                          ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                          ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
                          ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
                          ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_020), (nb055_alpha_dummy_021 x y)),
                          ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                          ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0002 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)),
        ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)),
        ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)),
        ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
        ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
        ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
        ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)),
        ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
        ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_028))
            (syn_cun (Class.cv (nb055_alpha_dummy_029)) (Class.cv (nb055_alpha_dummy_030))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_032 x y))
            (Class.cv (nb055_alpha_dummy_033 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_031 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_032 x y))
              (Class.cv (nb055_alpha_dummy_033 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)),
          ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)),
          ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)),
          ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
          ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
          ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
          ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)),
          ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
          ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
          ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part007`. -/


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
noncomputable def nb055_split_alpha_0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
        ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
        ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)),
        ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
        ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_022))
          (Class.cv (nb055_alpha_dummy_015))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_023))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_022)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_022)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_022))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y))
          (Class.cv (nb055_alpha_dummy_017 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_025 x y))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_024 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_024 x y)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0020) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0021 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0058) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0059 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0056) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0057 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_015))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0024) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0025 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0024) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0025 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0022) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb055_alpha_dummy_030), (nb055_alpha_dummy_033 x y)),
                                  ((nb055_alpha_dummy_029), (nb055_alpha_dummy_032 x y)),
                                  ((nb055_alpha_dummy_028), (nb055_alpha_dummy_031 x y)),
                                  ((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
                                  ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
                                  ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
                                  ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)),
                                  ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
                                  ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                                  ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                                  ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
                                  ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                                  ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                                  ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                                  ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                                  ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                                  ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                  ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                  ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055_split_alpha_0002 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
                      ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
                      ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
                      ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)),
                      ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
                      ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                      ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                      ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                      ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                      ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_026), (nb055_alpha_dummy_027 x y)),
                      ((nb055_alpha_dummy_022), (nb055_alpha_dummy_024 x y)),
                      ((nb055_alpha_dummy_023), (nb055_alpha_dummy_025 x y)),
                      ((nb055_alpha_dummy_048), (nb055_alpha_dummy_049 x y)),
                      ((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
                      ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                      ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                      ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                      ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                      ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb055_variable_occurrence_0 (x y : Var) :
    TAlphaClass
      [(nb055_alpha_dummy_015, (nb055_alpha_dummy_017 x y)),
        (nb055_alpha_dummy_014, (nb055_alpha_dummy_016 x y)),
        (nb055_alpha_dummy_044, (nb055_alpha_dummy_045 x y)),
        (nb055_alpha_dummy_018, (nb055_alpha_dummy_019 x y)),
        (nb055_alpha_dummy_007, (nb055_alpha_dummy_009 x y)),
        (nb055_alpha_dummy_006, (nb055_alpha_dummy_008 x y)),
        (nb055_alpha_dummy_012, (nb055_alpha_dummy_013 x y)),
        (nb055_alpha_dummy_010, (nb055_alpha_dummy_011 x y)),
        (nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_001) (Class.cv y) :=
  by
  have freshness0 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_015 :=
    by
    unfold nb055_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
  have freshness1 : y ≠ (nb055_alpha_dummy_017 x y) :=
    by
    unfold nb055_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
  have freshness2 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_014 :=
    by
    unfold nb055_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  have freshness3 : y ≠ (nb055_alpha_dummy_016 x y) :=
    by
    unfold nb055_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  have freshness4 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_044 :=
    by
    unfold nb055_alpha_dummy_044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0054) 0))
  have freshness5 : y ≠ (nb055_alpha_dummy_045 x y) :=
    by
    unfold nb055_alpha_dummy_045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0055 x y) 0))
  have freshness6 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_018 :=
    by
    unfold nb055_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0051) 0))
  have freshness7 : y ≠ (nb055_alpha_dummy_019 x y) :=
    by
    unfold nb055_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0053 x y) 0))
  have freshness8 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_007 :=
    by
    unfold nb055_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 1))
  have freshness9 : y ≠ (nb055_alpha_dummy_009 x y) :=
    by
    unfold nb055_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 1))
  have freshness10 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_006 :=
    by
    unfold nb055_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0044) 0))
  have freshness11 : y ≠ (nb055_alpha_dummy_008 x y) :=
    by
    unfold nb055_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0046 x y) 0))
  have freshness12 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_012 :=
    by
    unfold nb055_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0048) 0))
  have freshness13 : y ≠ (nb055_alpha_dummy_013 x y) :=
    by
    unfold nb055_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0049 x y) 0))
  have freshness14 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_010 :=
    by
    unfold nb055_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0045) 0))
  have freshness15 : y ≠ (nb055_alpha_dummy_011 x y) :=
    by
    unfold nb055_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0047 x y) 0))
  have freshness16 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0))
  have freshness17 : y ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0))
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
noncomputable def nb055_variable_occurrence_1 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb055_alpha_dummy_015, (nb055_alpha_dummy_017 x y)),
        (nb055_alpha_dummy_014, (nb055_alpha_dummy_016 x y)),
        (nb055_alpha_dummy_020, (nb055_alpha_dummy_021 x y)),
        (nb055_alpha_dummy_018, (nb055_alpha_dummy_019 x y)),
        (nb055_alpha_dummy_007, (nb055_alpha_dummy_009 x y)),
        (nb055_alpha_dummy_006, (nb055_alpha_dummy_008 x y)),
        (nb055_alpha_dummy_012, (nb055_alpha_dummy_013 x y)),
        (nb055_alpha_dummy_010, (nb055_alpha_dummy_011 x y)),
        (nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_000) (Class.cv x) :=
  by
  have freshness0 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_015 :=
    by
    unfold nb055_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
  have freshness1 : x ≠ (nb055_alpha_dummy_017 x y) :=
    by
    unfold nb055_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
  have freshness2 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_014 :=
    by
    unfold nb055_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  have freshness3 : x ≠ (nb055_alpha_dummy_016 x y) :=
    by
    unfold nb055_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  have freshness4 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_020 :=
    by
    unfold nb055_alpha_dummy_020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0018) 0))
  have freshness5 : x ≠ (nb055_alpha_dummy_021 x y) :=
    by
    unfold nb055_alpha_dummy_021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0019 x y) 0))
  have freshness6 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_018 :=
    by
    unfold nb055_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0015) 0))
  have freshness7 : x ≠ (nb055_alpha_dummy_019 x y) :=
    by
    unfold nb055_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0017 x y) 0))
  have freshness8 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_007 :=
    by
    unfold nb055_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 1))
  have freshness9 : x ≠ (nb055_alpha_dummy_009 x y) :=
    by
    unfold nb055_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 1))
  have freshness10 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_006 :=
    by
    unfold nb055_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0008) 0))
  have freshness11 : x ≠ (nb055_alpha_dummy_008 x y) :=
    by
    unfold nb055_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0010 x y) 0))
  have freshness12 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_012 :=
    by
    unfold nb055_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0012) 0))
  have freshness13 : x ≠ (nb055_alpha_dummy_013 x y) :=
    by
    unfold nb055_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0013 x y) 0))
  have freshness14 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_010 :=
    by
    unfold nb055_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0009) 0))
  have freshness15 : x ≠ (nb055_alpha_dummy_011 x y) :=
    by
    unfold nb055_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0011 x y) 0))
  have freshness16 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0))
  have freshness17 : x ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0))
  have freshness18 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_001 :=
    by
    unfold nb055_alpha_dummy_000 nb055_alpha_dummy_001
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
noncomputable def nb055_split_alpha_0004 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
        ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_044))
          (Class.cab (nb055_alpha_dummy_014)
            (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_044))
            (Class.cab (nb055_alpha_dummy_014)
              (syn_wrex (nb055_alpha_dummy_015) (Class.cv (nb055_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_045 x y))
          (Class.cab (nb055_alpha_dummy_016 x y)
            (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055_alpha_dummy_045 x y))
            (Class.cab (nb055_alpha_dummy_016 x y)
              (syn_wrex (nb055_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb055_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb055_variable_occurrence_0 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0003 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0003 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
                          ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                          ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb055_variable_occurrence_0 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055_alpha_dummy_000))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0003 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0003 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb055_alpha_dummy_046), (nb055_alpha_dummy_047 x y)),
                            ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                            ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                            ((nb055_alpha_dummy_044), (nb055_alpha_dummy_045 x y)),
                            ((nb055_alpha_dummy_018), (nb055_alpha_dummy_019 x y)),
                            ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                            ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                            ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                            ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                            ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                            ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                            ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0005 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)),
        ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)),
        ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)),
        ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
        ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
        ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_056))
            (syn_cun (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_059 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_060 x y))
              (Class.cv (nb055_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)),
          ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)),
          ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)),
          ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
          ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
          ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
          ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0006 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_007))
          (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001))))
        (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
            (syn_cphi (Class.cv (nb055_alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_009 x y))
          (syn_cop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
            (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb055_variable_occurrence_1 x y dv_x_y))
                            (nb055_split_alpha_0001 x y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb055_variable_occurrence_1 x y dv_x_y))
                            (nb055_split_alpha_0001 x y)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0004 x y)))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cop (Class.cv (nb055_alpha_dummy_000))
                    (Class.cv (nb055_alpha_dummy_001)))).fv ∪
                ((Class.cv (nb055_alpha_dummy_002))).fv) (by decide)) (freshVar_injective
              (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb055_alpha_dummy_009 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0064) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0065 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0064) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0062) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb055_alpha_dummy_058),
        (nb055_alpha_dummy_061 x y)), ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)),
        ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)), ((nb055_alpha_dummy_054),
        (nb055_alpha_dummy_055 x y)), ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
        ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)), ((nb055_alpha_dummy_007),
        (nb055_alpha_dummy_009 x y)), ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)), ((nb055_alpha_dummy_010),
        (nb055_alpha_dummy_011 x y)), ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004),
        (nb055_alpha_dummy_005 x y))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb055_split_alpha_0005 x y))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
                              ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
                              ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
                              ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                              ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                              ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                              ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                              ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                              ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                              ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
                              ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
                              ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
                              ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                              ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                              ((nb055_alpha_dummy_012), (nb055_alpha_dummy_013 x y)),
                              ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                              ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                              ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                              ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part008`. -/


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
noncomputable def nb055_split_alpha_0007 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)),
        ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)),
        ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)),
        ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
        ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
        ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
        ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)),
        ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_056))
            (syn_cun (Class.cv (nb055_alpha_dummy_057)) (Class.cv (nb055_alpha_dummy_058))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_060 x y))
            (Class.cv (nb055_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_059 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_060 x y))
              (Class.cv (nb055_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)),
          ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)),
          ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)),
          ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
          ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
          ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
          ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)),
          ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
          ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
          ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
          ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
          ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0008 (x : Var) (y : Var) :
    TAlphaClass
      [((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)),
        ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
        ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Class.cab (nb055_alpha_dummy_051)
        (syn_wrex (nb055_alpha_dummy_050) (Class.cv (nb055_alpha_dummy_007))
          (Wff.classEq (Class.cv (nb055_alpha_dummy_051))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_050)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_050)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_050))))))
      (Class.cab (nb055_alpha_dummy_053 x y)
        (syn_wrex (nb055_alpha_dummy_052 x y) (Class.cv (nb055_alpha_dummy_009 x y))
          (Wff.classEq (Class.cv (nb055_alpha_dummy_053 x y))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_052 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_052 x y)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_052 x y)))))) :=
  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0060) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0061 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0090) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0091 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0089 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_007))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_009 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0064) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0065 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0064) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0065 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0062) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb055_alpha_dummy_058), (nb055_alpha_dummy_061 x y)),
                                    ((nb055_alpha_dummy_057), (nb055_alpha_dummy_060 x y)),
                                    ((nb055_alpha_dummy_056), (nb055_alpha_dummy_059 x y)),
                                    ((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
                                    ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
                                    ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
                                    ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)),
                                    ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
                                    ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                                    ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                                    ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
                                    ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                                    ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                    ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                    ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb055_split_alpha_0007 x y))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
                        ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
                        ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
                        ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)),
                        ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
                        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                        ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
                        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0063 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb055_alpha_dummy_054), (nb055_alpha_dummy_055 x y)),
                        ((nb055_alpha_dummy_050), (nb055_alpha_dummy_052 x y)),
                        ((nb055_alpha_dummy_051), (nb055_alpha_dummy_053 x y)),
                        ((nb055_alpha_dummy_076), (nb055_alpha_dummy_077 x y)),
                        ((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
                        ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                        ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                        ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
                        ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def nb055_variable_occurrence_2 (x y : Var) :
    TAlphaClass
      [(nb055_alpha_dummy_007, (nb055_alpha_dummy_009 x y)),
        (nb055_alpha_dummy_006, (nb055_alpha_dummy_008 x y)),
        (nb055_alpha_dummy_072, (nb055_alpha_dummy_073 x y)),
        (nb055_alpha_dummy_010, (nb055_alpha_dummy_011 x y)),
        (nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_002) (Class.cv (nb055_alpha_dummy_003 x y)) :=
  by
  have freshness0 : nb055_alpha_dummy_002 ≠ nb055_alpha_dummy_007 :=
    by
    unfold nb055_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 1))
  have freshness1 : (nb055_alpha_dummy_003 x y) ≠ (nb055_alpha_dummy_009 x y) :=
    by
    unfold nb055_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 1))
  have freshness2 : nb055_alpha_dummy_002 ≠ nb055_alpha_dummy_006 :=
    by
    unfold nb055_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0082) 0))
  have freshness3 : (nb055_alpha_dummy_003 x y) ≠ (nb055_alpha_dummy_008 x y) :=
    by
    unfold nb055_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0084 x y) 0))
  have freshness4 : nb055_alpha_dummy_002 ≠ nb055_alpha_dummy_072 :=
    by
    unfold nb055_alpha_dummy_072
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0086) 0))
  have freshness5 : (nb055_alpha_dummy_003 x y) ≠ (nb055_alpha_dummy_073 x y) :=
    by
    unfold nb055_alpha_dummy_073
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0087 x y) 0))
  have freshness6 : nb055_alpha_dummy_002 ≠ nb055_alpha_dummy_010 :=
    by
    unfold nb055_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0083) 0))
  have freshness7 : (nb055_alpha_dummy_003 x y) ≠ (nb055_alpha_dummy_011 x y) :=
    by
    unfold nb055_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0085 x y) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

@[expose]
noncomputable def nb055_split_alpha_0009 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_010)) (syn_ccompl
            (Class.cab (nb055_alpha_dummy_006) (syn_wrex (nb055_alpha_dummy_007)
                (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_007)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055_alpha_dummy_010)) (syn_ccompl
              (Class.cab (nb055_alpha_dummy_006)
                (syn_wrex (nb055_alpha_dummy_007) (Class.cv (nb055_alpha_dummy_002))
                  (Wff.classEq (Class.cv (nb055_alpha_dummy_006))
                    (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_007)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_011 x y)) (syn_ccompl
            (Class.cab (nb055_alpha_dummy_008 x y)
              (syn_wrex (nb055_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055_alpha_dummy_011 x y)) (syn_ccompl
              (Class.cab (nb055_alpha_dummy_008 x y) (syn_wrex (nb055_alpha_dummy_009 x y)
                  (Class.cv (nb055_alpha_dummy_003 x y))
                  (Wff.classEq (Class.cv (nb055_alpha_dummy_008 x y))
                    (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_009 x y)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb055_split_alpha_0006 x y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb055_split_alpha_0006 x y dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb055_variable_occurrence_2 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((syn_cop (Class.cv (nb055_alpha_dummy_000))
                                    (Class.cv (nb055_alpha_dummy_001)))).fv ∪
                                ((Class.cv (nb055_alpha_dummy_002))).fv) (by decide))
                            (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055_split_alpha_0008 x y)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055_split_alpha_0008 x y))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
                                    ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                                    ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                                    ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
                                    ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                                    ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                    ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                    ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb055_variable_occurrence_2 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((syn_cop (Class.cv (nb055_alpha_dummy_000))
                                    (Class.cv (nb055_alpha_dummy_001)))).fv ∪
                                ((Class.cv (nb055_alpha_dummy_002))).fv) (by decide))
                            (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb055_alpha_dummy_003 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055_split_alpha_0008 x y)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb055_split_alpha_0008 x y))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb055_alpha_dummy_074), (nb055_alpha_dummy_075 x y)),
                                    ((nb055_alpha_dummy_007), (nb055_alpha_dummy_009 x y)),
                                    ((nb055_alpha_dummy_006), (nb055_alpha_dummy_008 x y)),
                                    ((nb055_alpha_dummy_072), (nb055_alpha_dummy_073 x y)),
                                    ((nb055_alpha_dummy_010), (nb055_alpha_dummy_011 x y)),
                                    ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                    ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                    ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part009`. -/


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
noncomputable def nb055_split_alpha_0010 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)),
        ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)),
        ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)),
        ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
        ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
        ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
        ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
        ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
        ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)),
        ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_096))
            (syn_cun (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_099 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_100 x y))
              (Class.cv (nb055_alpha_dummy_101 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)),
          ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)),
          ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)),
          ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
          ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
          ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
          ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
          ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
          ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)),
          ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0011 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
        ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
        ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)),
        ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
        (syn_cphi (Class.cv (nb055_alpha_dummy_083))))
      (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
        (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
            ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_083))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_085 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0106) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0107 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0106) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0107 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0104) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb055_alpha_dummy_098),
                                        (nb055_alpha_dummy_101 x y)), ((nb055_alpha_dummy_097),
                                        (nb055_alpha_dummy_100 x y)), ((nb055_alpha_dummy_096),
                                        (nb055_alpha_dummy_099 x y)), ((nb055_alpha_dummy_094),
                                        (nb055_alpha_dummy_095 x y)), ((nb055_alpha_dummy_090),
                                        (nb055_alpha_dummy_092 x y)), ((nb055_alpha_dummy_091),
                                        (nb055_alpha_dummy_093 x y)), ((nb055_alpha_dummy_083),
                                        (nb055_alpha_dummy_085 x y)), ((nb055_alpha_dummy_082),
                                        (nb055_alpha_dummy_084 x y)), ((nb055_alpha_dummy_088),
                                        (nb055_alpha_dummy_089 x y)), ((nb055_alpha_dummy_086),
                                        (nb055_alpha_dummy_087 x y)), ((nb055_alpha_dummy_015),
                                        (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014),
                                        (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080),
                                        (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002),
                                        (nb055_alpha_dummy_003 x y)),
                                      ((nb055_alpha_dummy_001), y),
                                      ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004),
                                        (nb055_alpha_dummy_005 x y))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055_split_alpha_0010 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
                          ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
                          ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
                          ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                          ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                          ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)),
                          ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
                          ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
                          ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
                          ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                          ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                          ((nb055_alpha_dummy_088), (nb055_alpha_dummy_089 x y)),
                          ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0012 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)),
        ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)),
        ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)),
        ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
        ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
        ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
        ((nb055_alpha_dummy_116), (nb055_alpha_dummy_117 x y)),
        ((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
        ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
        ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
        ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
        ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_096))
            (syn_cun (Class.cv (nb055_alpha_dummy_097)) (Class.cv (nb055_alpha_dummy_098))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_100 x y))
            (Class.cv (nb055_alpha_dummy_101 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_099 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_100 x y))
              (Class.cv (nb055_alpha_dummy_101 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0110) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0111 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0108) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0109 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0114) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0115 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0113 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)),
          ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)),
          ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)),
          ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
          ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
          ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
          ((nb055_alpha_dummy_116), (nb055_alpha_dummy_117 x y)),
          ((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
          ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
          ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
          ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
          ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0118) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0119 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0116) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0117 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_090))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_092 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0122) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0123 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0120) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0121 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0013 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
        ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
        ((nb055_alpha_dummy_116), (nb055_alpha_dummy_117 x y)),
        ((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
        ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
        ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
        ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
        ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_090))
          (Class.cv (nb055_alpha_dummy_083))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_091))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_090)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_090)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_090))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y))
          (Class.cv (nb055_alpha_dummy_085 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_093 x y))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_092 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_092 x y)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_092 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0102) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0103 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0132) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0133 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0130) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0131 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_083))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_085 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0106) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0107 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0106) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0107 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0104) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb055_alpha_dummy_098), (nb055_alpha_dummy_101 x y)),
                                  ((nb055_alpha_dummy_097), (nb055_alpha_dummy_100 x y)),
                                  ((nb055_alpha_dummy_096), (nb055_alpha_dummy_099 x y)),
                                  ((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
                                  ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
                                  ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
                                  ((nb055_alpha_dummy_116), (nb055_alpha_dummy_117 x y)),
                                  ((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
                                  ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                                  ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                                  ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
                                  ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                                  ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                                  ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                                  ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                                  ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                  ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                  ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055_split_alpha_0012 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
                      ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
                      ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
                      ((nb055_alpha_dummy_116), (nb055_alpha_dummy_117 x y)),
                      ((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
                      ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                      ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                      ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
                      ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0104) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0105 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_094), (nb055_alpha_dummy_095 x y)),
                      ((nb055_alpha_dummy_090), (nb055_alpha_dummy_092 x y)),
                      ((nb055_alpha_dummy_091), (nb055_alpha_dummy_093 x y)),
                      ((nb055_alpha_dummy_116), (nb055_alpha_dummy_117 x y)),
                      ((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
                      ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                      ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                      ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
                      ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part010`. -/


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
noncomputable def nb055_split_alpha_0014 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
        ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_112))
          (Class.cab (nb055_alpha_dummy_082)
            (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_112))
            (Class.cab (nb055_alpha_dummy_082)
              (syn_wrex (nb055_alpha_dummy_083) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_082))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_083)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_113 x y))
          (Class.cab (nb055_alpha_dummy_084 x y)
            (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055_alpha_dummy_113 x y))
            (Class.cab (nb055_alpha_dummy_084 x y)
              (syn_wrex (nb055_alpha_dummy_085 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_084 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_085 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0128) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0129 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0125) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0127 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_015))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0013 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0013 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
                          ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                          ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                          ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
                          ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0124) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0126 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0128) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0129 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0125) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0127 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055_alpha_dummy_014))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_015))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0013 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0013 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb055_alpha_dummy_114), (nb055_alpha_dummy_115 x y)),
                            ((nb055_alpha_dummy_083), (nb055_alpha_dummy_085 x y)),
                            ((nb055_alpha_dummy_082), (nb055_alpha_dummy_084 x y)),
                            ((nb055_alpha_dummy_112), (nb055_alpha_dummy_113 x y)),
                            ((nb055_alpha_dummy_086), (nb055_alpha_dummy_087 x y)),
                            ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                            ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                            ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                            ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                            ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                            ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0015 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)),
        ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)),
        ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)),
        ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
        ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
        ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
        ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
        ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
        ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)),
        ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_132))
            (syn_cun (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_135 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_136 x y))
              (Class.cv (nb055_alpha_dummy_137 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)),
          ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)),
          ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)),
          ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
          ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
          ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
          ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
          ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
          ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)),
          ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0016 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
        ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
        ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)),
        ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
        (syn_cphi (Class.cv (nb055_alpha_dummy_119))))
      (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
        (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055_alpha_dummy_014))).fv ∪ ((Class.cv (nb055_alpha_dummy_078))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
            ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_119))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_121 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0144) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0145 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0144) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0145 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0142) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb055_alpha_dummy_134),
                                        (nb055_alpha_dummy_137 x y)), ((nb055_alpha_dummy_133),
                                        (nb055_alpha_dummy_136 x y)), ((nb055_alpha_dummy_132),
                                        (nb055_alpha_dummy_135 x y)), ((nb055_alpha_dummy_130),
                                        (nb055_alpha_dummy_131 x y)), ((nb055_alpha_dummy_126),
                                        (nb055_alpha_dummy_128 x y)), ((nb055_alpha_dummy_127),
                                        (nb055_alpha_dummy_129 x y)), ((nb055_alpha_dummy_119),
                                        (nb055_alpha_dummy_121 x y)), ((nb055_alpha_dummy_118),
                                        (nb055_alpha_dummy_120 x y)), ((nb055_alpha_dummy_124),
                                        (nb055_alpha_dummy_125 x y)), ((nb055_alpha_dummy_122),
                                        (nb055_alpha_dummy_123 x y)), ((nb055_alpha_dummy_078),
                                        (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015),
                                        (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014),
                                        (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080),
                                        (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002),
                                        (nb055_alpha_dummy_003 x y)),
                                      ((nb055_alpha_dummy_001), y),
                                      ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004),
                                        (nb055_alpha_dummy_005 x y))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055_split_alpha_0015 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
                          ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
                          ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
                          ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                          ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                          ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)),
                          ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
                          ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
                          ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
                          ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                          ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                          ((nb055_alpha_dummy_124), (nb055_alpha_dummy_125 x y)),
                          ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part011`. -/


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
noncomputable def nb055_split_alpha_0017 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)),
        ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)),
        ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)),
        ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
        ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
        ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
        ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)),
        ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
        ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
        ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
        ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
        ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_132))
            (syn_cun (Class.cv (nb055_alpha_dummy_133)) (Class.cv (nb055_alpha_dummy_134))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_136 x y))
            (Class.cv (nb055_alpha_dummy_137 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_135 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_136 x y))
              (Class.cv (nb055_alpha_dummy_137 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0148) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0149 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0146) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0147 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0152) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0153 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0150) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0151 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)),
          ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)),
          ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)),
          ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
          ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
          ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
          ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)),
          ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
          ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
          ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
          ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
          ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0156) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0157 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0154) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0155 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_126))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_128 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0160) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0161 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0158) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0159 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0018 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
        ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
        ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)),
        ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
        ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
        ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
        ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
        ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_126))
          (Class.cv (nb055_alpha_dummy_119))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_127))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_126)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_126)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_126))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y))
          (Class.cv (nb055_alpha_dummy_121 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_129 x y))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_128 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_128 x y)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_128 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0140) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0141 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0170) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0171 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0168) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0169 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_119))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_121 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0144) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0145 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0144) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0145 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0142) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb055_alpha_dummy_134), (nb055_alpha_dummy_137 x y)),
                                  ((nb055_alpha_dummy_133), (nb055_alpha_dummy_136 x y)),
                                  ((nb055_alpha_dummy_132), (nb055_alpha_dummy_135 x y)),
                                  ((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
                                  ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
                                  ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
                                  ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)),
                                  ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
                                  ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                                  ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                                  ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
                                  ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                                  ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                                  ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                                  ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                                  ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                                  ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                  ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                  ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055_split_alpha_0017 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
                      ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
                      ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
                      ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)),
                      ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
                      ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                      ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                      ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
                      ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                      ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0142) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0143 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_130), (nb055_alpha_dummy_131 x y)),
                      ((nb055_alpha_dummy_126), (nb055_alpha_dummy_128 x y)),
                      ((nb055_alpha_dummy_127), (nb055_alpha_dummy_129 x y)),
                      ((nb055_alpha_dummy_152), (nb055_alpha_dummy_153 x y)),
                      ((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
                      ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                      ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                      ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
                      ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                      ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb055_split_alpha_0019 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
        ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_148))
          (Class.cab (nb055_alpha_dummy_118)
            (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_148))
            (Class.cab (nb055_alpha_dummy_118)
              (syn_wrex (nb055_alpha_dummy_119) (Class.cv (nb055_alpha_dummy_078))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_118))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_119)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_149 x y))
          (Class.cab (nb055_alpha_dummy_120 x y)
            (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055_alpha_dummy_149 x y))
            (Class.cab (nb055_alpha_dummy_120 x y)
              (syn_wrex (nb055_alpha_dummy_121 x y) (Class.cv (nb055_alpha_dummy_079 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_120 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_121 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0166) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0167 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0163) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0165 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_014))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_078))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0018 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0018 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
                          ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                          ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                          ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
                          ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0162) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0164 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0166) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0167 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0163) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0165 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055_alpha_dummy_014))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_078))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb055_alpha_dummy_016 x y))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_079 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0018 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0018 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb055_alpha_dummy_150), (nb055_alpha_dummy_151 x y)),
                            ((nb055_alpha_dummy_119), (nb055_alpha_dummy_121 x y)),
                            ((nb055_alpha_dummy_118), (nb055_alpha_dummy_120 x y)),
                            ((nb055_alpha_dummy_148), (nb055_alpha_dummy_149 x y)),
                            ((nb055_alpha_dummy_122), (nb055_alpha_dummy_123 x y)),
                            ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                            ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                            ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                            ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                            ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                            ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                            ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0020 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)),
        ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)),
        ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)),
        ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
        ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
        ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
        ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
        ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
        ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)),
        ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_168))
            (syn_cun (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_171 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_172 x y))
              (Class.cv (nb055_alpha_dummy_173 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)),
          ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)),
          ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)),
          ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
          ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
          ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
          ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
          ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
          ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)),
          ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part012`. -/


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
noncomputable def nb055_split_alpha_0021 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
        ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
        ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)),
        ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
        (syn_cphi (Class.cv (nb055_alpha_dummy_155))))
      (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
        (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb055_alpha_dummy_078))).fv ∪ ((Class.cv (nb055_alpha_dummy_015))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
            ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_155))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb055_alpha_dummy_157 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0184) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0185 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0184) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0185 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0182) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb055_alpha_dummy_170),
                                        (nb055_alpha_dummy_173 x y)), ((nb055_alpha_dummy_169),
                                        (nb055_alpha_dummy_172 x y)), ((nb055_alpha_dummy_168),
                                        (nb055_alpha_dummy_171 x y)), ((nb055_alpha_dummy_166),
                                        (nb055_alpha_dummy_167 x y)), ((nb055_alpha_dummy_162),
                                        (nb055_alpha_dummy_164 x y)), ((nb055_alpha_dummy_163),
                                        (nb055_alpha_dummy_165 x y)), ((nb055_alpha_dummy_155),
                                        (nb055_alpha_dummy_157 x y)), ((nb055_alpha_dummy_154),
                                        (nb055_alpha_dummy_156 x y)), ((nb055_alpha_dummy_160),
                                        (nb055_alpha_dummy_161 x y)), ((nb055_alpha_dummy_158),
                                        (nb055_alpha_dummy_159 x y)), ((nb055_alpha_dummy_078),
                                        (nb055_alpha_dummy_079 x y)), ((nb055_alpha_dummy_015),
                                        (nb055_alpha_dummy_017 x y)), ((nb055_alpha_dummy_014),
                                        (nb055_alpha_dummy_016 x y)), ((nb055_alpha_dummy_080),
                                        (nb055_alpha_dummy_081 x y)), ((nb055_alpha_dummy_002),
                                        (nb055_alpha_dummy_003 x y)),
                                      ((nb055_alpha_dummy_001), y),
                                      ((nb055_alpha_dummy_000), x), ((nb055_alpha_dummy_004),
                                        (nb055_alpha_dummy_005 x y))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb055_split_alpha_0020 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
                          ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
                          ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
                          ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                          ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                          ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)),
                          ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
                          ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
                          ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
                          ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                          ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                          ((nb055_alpha_dummy_160), (nb055_alpha_dummy_161 x y)),
                          ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0022 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)),
        ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)),
        ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)),
        ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
        ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
        ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
        ((nb055_alpha_dummy_188), (nb055_alpha_dummy_189 x y)),
        ((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
        ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
        ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
        ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
        ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb055_alpha_dummy_168))
            (syn_cun (Class.cv (nb055_alpha_dummy_169)) (Class.cv (nb055_alpha_dummy_170))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb055_alpha_dummy_172 x y))
            (Class.cv (nb055_alpha_dummy_173 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_171 x y))
            (syn_cun (Class.cv (nb055_alpha_dummy_172 x y))
              (Class.cv (nb055_alpha_dummy_173 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0188) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0189 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0187 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0192) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0193 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0191 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)),
          ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)),
          ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)),
          ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
          ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
          ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
          ((nb055_alpha_dummy_188), (nb055_alpha_dummy_189 x y)),
          ((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
          ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
          ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
          ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
          ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0196) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0197 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0194) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0195 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_162))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb055_alpha_dummy_164 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0200) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0201 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0198) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0199 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb055_split_alpha_0023 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
        ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
        ((nb055_alpha_dummy_188), (nb055_alpha_dummy_189 x y)),
        ((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
        ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
        ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
        ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
        ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_162))
          (Class.cv (nb055_alpha_dummy_155))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_163))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_162)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_162)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_162))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y))
          (Class.cv (nb055_alpha_dummy_157 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb055_alpha_dummy_165 x y))
            (syn_cif (Wff.classMem (Class.cv (nb055_alpha_dummy_164 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb055_alpha_dummy_164 x y)) (syn_c1c))
              (Class.cv (nb055_alpha_dummy_164 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0180) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0181 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0210) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0211 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0208) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0209 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_155))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb055_alpha_dummy_157 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0184) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0185 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0184) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb055_support_mem_0185 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0182) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb055_alpha_dummy_170), (nb055_alpha_dummy_173 x y)),
                                  ((nb055_alpha_dummy_169), (nb055_alpha_dummy_172 x y)),
                                  ((nb055_alpha_dummy_168), (nb055_alpha_dummy_171 x y)),
                                  ((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
                                  ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
                                  ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
                                  ((nb055_alpha_dummy_188), (nb055_alpha_dummy_189 x y)),
                                  ((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
                                  ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                                  ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                                  ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
                                  ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                                  ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                                  ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                                  ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                                  ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                                  ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                                  ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                                  ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb055_split_alpha_0022 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
                      ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
                      ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
                      ((nb055_alpha_dummy_188), (nb055_alpha_dummy_189 x y)),
                      ((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
                      ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                      ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                      ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
                      ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                      ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0182) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0183 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb055_alpha_dummy_166), (nb055_alpha_dummy_167 x y)),
                      ((nb055_alpha_dummy_162), (nb055_alpha_dummy_164 x y)),
                      ((nb055_alpha_dummy_163), (nb055_alpha_dummy_165 x y)),
                      ((nb055_alpha_dummy_188), (nb055_alpha_dummy_189 x y)),
                      ((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
                      ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                      ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                      ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
                      ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                      ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                      ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                      ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                      ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                      ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                      ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                      ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb055_split_alpha_0024 (x : Var) (y : Var) :
    TAlphaWff
      [((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
        ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
        ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_184))
          (Class.cab (nb055_alpha_dummy_154)
            (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb055_alpha_dummy_184))
            (Class.cab (nb055_alpha_dummy_154)
              (syn_wrex (nb055_alpha_dummy_155) (Class.cv (nb055_alpha_dummy_015))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_154))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_155)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb055_alpha_dummy_185 x y))
          (Class.cab (nb055_alpha_dummy_156 x y)
            (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
              (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb055_alpha_dummy_185 x y))
            (Class.cab (nb055_alpha_dummy_156 x y)
              (syn_wrex (nb055_alpha_dummy_157 x y) (Class.cv (nb055_alpha_dummy_017 x y))
                (Wff.classEq (Class.cv (nb055_alpha_dummy_156 x y))
                  (syn_cun (syn_cphi (Class.cv (nb055_alpha_dummy_157 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0206) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0207 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0203) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0205 x y) 0))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb055_alpha_dummy_000))).fv ∪
                              ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide))
                          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb055_alpha_dummy_078))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_015))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
                      ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0023 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb055_split_alpha_0023 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
                          ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                          ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                          ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
                          ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                          ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                          ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                          ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                          ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                          ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                          ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                          ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0202) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0204 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0206) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0207 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0203) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0205 x y) 0))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb055_alpha_dummy_000))).fv ∪
                                ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb055_alpha_dummy_078))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_015))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb055_alpha_dummy_079 x y))).fv ∪
                        ((Class.cv (nb055_alpha_dummy_017 x y))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0023 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb055_split_alpha_0023 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb055_alpha_dummy_186), (nb055_alpha_dummy_187 x y)),
                            ((nb055_alpha_dummy_155), (nb055_alpha_dummy_157 x y)),
                            ((nb055_alpha_dummy_154), (nb055_alpha_dummy_156 x y)),
                            ((nb055_alpha_dummy_184), (nb055_alpha_dummy_185 x y)),
                            ((nb055_alpha_dummy_158), (nb055_alpha_dummy_159 x y)),
                            ((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
                            ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
                            ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
                            ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
                            ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                            ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                            ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C055C001Part013`. -/


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
noncomputable def nb055_compose_occurrence_0 (x y : Var) :
    TAlphaClass
      [(nb055_alpha_dummy_078, (nb055_alpha_dummy_079 x y)),
        (nb055_alpha_dummy_015, (nb055_alpha_dummy_017 x y)),
        (nb055_alpha_dummy_014, (nb055_alpha_dummy_016 x y)),
        (nb055_alpha_dummy_080, (nb055_alpha_dummy_081 x y)),
        (nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_001) (Class.cv y) :=
  by
  have freshness0 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_078 :=
    by
    unfold nb055_alpha_dummy_078
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 2))
  have freshness1 : y ≠ (nb055_alpha_dummy_079 x y) :=
    by
    unfold nb055_alpha_dummy_079
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 2))
  have freshness2 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_015 :=
    by
    unfold nb055_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 1))
  have freshness3 : y ≠ (nb055_alpha_dummy_017 x y) :=
    by
    unfold nb055_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 1))
  have freshness4 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_014 :=
    by
    unfold nb055_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0050) 0))
  have freshness5 : y ≠ (nb055_alpha_dummy_016 x y) :=
    by
    unfold nb055_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0052 x y) 0))
  have freshness6 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_080 :=
    by
    unfold nb055_alpha_dummy_080
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0172) 0))
  have freshness7 : y ≠ (nb055_alpha_dummy_081 x y) :=
    by
    unfold nb055_alpha_dummy_081
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0173 x y) 0))
  have freshness8 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0))
  have freshness9 : y ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7
                (TAlphaVar.there freshness8 freshness9 (TAlphaVar.here _ _ _)))))))

@[expose]
noncomputable def nb055_compose_occurrence_1 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb055_alpha_dummy_078, (nb055_alpha_dummy_079 x y)),
        (nb055_alpha_dummy_015, (nb055_alpha_dummy_017 x y)),
        (nb055_alpha_dummy_014, (nb055_alpha_dummy_016 x y)),
        (nb055_alpha_dummy_080, (nb055_alpha_dummy_081 x y)),
        (nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_000) (Class.cv x) :=
  by
  have freshness0 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_078 :=
    by
    unfold nb055_alpha_dummy_078
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 2))
  have freshness1 : x ≠ (nb055_alpha_dummy_079 x y) :=
    by
    unfold nb055_alpha_dummy_079
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 2))
  have freshness2 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_015 :=
    by
    unfold nb055_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 1))
  have freshness3 : x ≠ (nb055_alpha_dummy_017 x y) :=
    by
    unfold nb055_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 1))
  have freshness4 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_014 :=
    by
    unfold nb055_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0014) 0))
  have freshness5 : x ≠ (nb055_alpha_dummy_016 x y) :=
    by
    unfold nb055_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0016 x y) 0))
  have freshness6 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_080 :=
    by
    unfold nb055_alpha_dummy_080
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0212) 0))
  have freshness7 : x ≠ (nb055_alpha_dummy_081 x y) :=
    by
    unfold nb055_alpha_dummy_081
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0213 x y) 0))
  have freshness8 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0))
  have freshness9 : x ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0))
  have freshness10 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_001 :=
    by
    unfold nb055_alpha_dummy_000 nb055_alpha_dummy_001
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness11 : x ≠ y := by exact dv_x_y
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11 (TAlphaVar.here _ _ _))))))))

@[expose]
noncomputable def nb055_split_alpha_0025 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055_alpha_dummy_078), (nb055_alpha_dummy_079 x y)),
        ((nb055_alpha_dummy_015), (nb055_alpha_dummy_017 x y)),
        ((nb055_alpha_dummy_014), (nb055_alpha_dummy_016 x y)),
        ((nb055_alpha_dummy_080), (nb055_alpha_dummy_081 x y)),
        ((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (syn_wbr (Class.cv (nb055_alpha_dummy_014)) (Class.cv (nb055_alpha_dummy_001))
          (Class.cv (nb055_alpha_dummy_078))) (Wff.neg
          (syn_wbr (Class.cv (nb055_alpha_dummy_078)) (Class.cv (nb055_alpha_dummy_000))
            (Class.cv (nb055_alpha_dummy_015)))))
      (Wff.imp (syn_wbr (Class.cv (nb055_alpha_dummy_016 x y)) (Class.cv y)
          (Class.cv (nb055_alpha_dummy_079 x y))) (Wff.neg
          (syn_wbr (Class.cv (nb055_alpha_dummy_079 x y)) (Class.cv x)
            (Class.cv (nb055_alpha_dummy_017 x y))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0134) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0134) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0138) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0139 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0135) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0137 x y) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪
        ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb055_split_alpha_0016 x y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0134) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb055_support_mem_0136 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0134) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0136 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0138) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0139 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0135) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0137 x y) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv)
        (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb055_alpha_dummy_000))).fv ∪
        ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide)) (freshVar_injective
        (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb055_split_alpha_0016 x y)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0019 x y))))))))
      (nb055_compose_occurrence_0 x y)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0174) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0174) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0178) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0179 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0175) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0177 x y) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb055_split_alpha_0021 x y)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0174) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb055_support_mem_0176 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0174) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb055_support_mem_0176 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0178) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0179 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0175) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0177 x y) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb055_split_alpha_0021 x y)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0024 x y))))))))
        (nb055_compose_occurrence_1 x y dv_x_y))))

@[expose]
noncomputable def nb055_compose_occurrence_2 (x y : Var) :
    TAlphaClass
      [(nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_004) (Class.cv (nb055_alpha_dummy_005 x y)) :=
  by
  have freshness0 : nb055_alpha_dummy_004 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0004) 0)))
  have freshness1 : (nb055_alpha_dummy_005 x y) ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0005 x y) 0)))
  have freshness2 : nb055_alpha_dummy_004 ≠ nb055_alpha_dummy_001 :=
    by
    unfold nb055_alpha_dummy_004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0002) 0)))
  have freshness3 : (nb055_alpha_dummy_005 x y) ≠ y :=
    by
    unfold nb055_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0003 x y) 0)))
  have freshness4 : nb055_alpha_dummy_004 ≠ nb055_alpha_dummy_000 :=
    by
    unfold nb055_alpha_dummy_004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0000) 0)))
  have freshness5 : (nb055_alpha_dummy_005 x y) ≠ x :=
    by
    unfold nb055_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0001 x y) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3
            (TAlphaVar.there freshness4 freshness5 (TAlphaVar.here _ _ _)))))

@[expose]
noncomputable def nb055_compose_root_occurrence_0 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_000) (Class.cv x) :=
  by
  have freshness0 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0006) 0))
  have freshness1 : x ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0007 x y) 0))
  have freshness2 : nb055_alpha_dummy_000 ≠ nb055_alpha_dummy_001 :=
    by
    unfold nb055_alpha_dummy_000 nb055_alpha_dummy_001
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness3 : x ≠ y := by exact dv_x_y
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb055_compose_root_occurrence_1 (x y : Var) :
    TAlphaClass
      [(nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_001) (Class.cv y) :=
  by
  have freshness0 : nb055_alpha_dummy_001 ≠ nb055_alpha_dummy_002 :=
    by
    unfold nb055_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0042) 0))
  have freshness1 : y ≠ (nb055_alpha_dummy_003 x y) :=
    by
    unfold nb055_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0043 x y) 0))
  with_reducible
    exact (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1 (TAlphaVar.here _ _ _)))

@[expose]
noncomputable def nb055_compose_occurrence_3 (x y : Var) :
    TAlphaClass
      [(nb055_alpha_dummy_015, (nb055_alpha_dummy_017 x y)),
        (nb055_alpha_dummy_014, (nb055_alpha_dummy_016 x y)),
        (nb055_alpha_dummy_080, (nb055_alpha_dummy_081 x y)),
        (nb055_alpha_dummy_002, (nb055_alpha_dummy_003 x y)), (nb055_alpha_dummy_001, y),
        (nb055_alpha_dummy_000, x), (nb055_alpha_dummy_004, (nb055_alpha_dummy_005 x y))]
      (Class.cv nb055_alpha_dummy_080) (Class.cv (nb055_alpha_dummy_081 x y)) :=
  by
  have freshness0 : nb055_alpha_dummy_080 ≠ nb055_alpha_dummy_015 :=
    by
    unfold nb055_alpha_dummy_080
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0094) 0)))
  have freshness1 : (nb055_alpha_dummy_081 x y) ≠ (nb055_alpha_dummy_017 x y) :=
    by
    unfold nb055_alpha_dummy_081
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0095 x y) 0)))
  have freshness2 : nb055_alpha_dummy_080 ≠ nb055_alpha_dummy_014 :=
    by
    unfold nb055_alpha_dummy_080
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0092) 0)))
  have freshness3 : (nb055_alpha_dummy_081 x y) ≠ (nb055_alpha_dummy_016 x y) :=
    by
    unfold nb055_alpha_dummy_081
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb055_support_mem_0093 x y) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb055_split_alpha_0026 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
        ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
        ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq (Class.cv (nb055_alpha_dummy_004)) (syn_cop
            (syn_cop (Class.cv (nb055_alpha_dummy_000)) (Class.cv (nb055_alpha_dummy_001)))
            (Class.cv (nb055_alpha_dummy_002)))) (Wff.neg (syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb055_alpha_dummy_000)) (syn_cvv))
              (Wff.classMem (Class.cv (nb055_alpha_dummy_001)) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_002))
              (syn_ccom (Class.cv (nb055_alpha_dummy_000))
                (Class.cv (nb055_alpha_dummy_001)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb055_alpha_dummy_005 x y))
          (syn_cop (syn_cop (Class.cv x) (Class.cv y)) (Class.cv (nb055_alpha_dummy_003 x y))))
        (Wff.neg (syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv))
              (Wff.classMem (Class.cv y) (syn_cvv)))
            (Wff.classEq (Class.cv (nb055_alpha_dummy_003 x y))
              (syn_ccom (Class.cv x) (Class.cv y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (nb055_compose_occurrence_2 x y) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb055_split_alpha_0009 x y dv_x_y))))) (TAlphaWff.neg
      (TAlphaWff.conj (TAlphaWff.conj
          (TAlphaWff.classMem (nb055_compose_root_occurrence_0 x y dv_x_y)
            (TAlphaClass.refl_of_closed [((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
              (syn_cvv) (by simp only [fv_syn_cvv])))
          (TAlphaWff.classMem (nb055_compose_root_occurrence_1 x y) (TAlphaClass.refl_of_closed
              [((nb055_alpha_dummy_002), (nb055_alpha_dummy_003 x y)),
                ((nb055_alpha_dummy_001), y), ((nb055_alpha_dummy_000), x),
                ((nb055_alpha_dummy_004), (nb055_alpha_dummy_005 x y))]
              (syn_cvv) (by simp only [fv_syn_cvv]))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classEq (nb055_compose_occurrence_3 x y) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0101 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0097) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0099 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb055_split_alpha_0011 x y))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb055_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0098 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0101 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0097) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb055_support_mem_0099 x y) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb055_alpha_dummy_000))).fv ∪ ((Class.cv (nb055_alpha_dummy_001))).fv) (by decide))
        (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb055_split_alpha_0011 x y)))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb055_split_alpha_0014 x y)))))))))
                  (TAlphaWff.ex (TAlphaWff.neg (nb055_split_alpha_0025 x y dv_x_y)))))))))))

@[expose]
noncomputable def nominal_df_compose (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_ccompose)
        (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_ccom (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.ex (TAlphaWff.neg (nb055_split_alpha_0026 x y dv_x_y))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
