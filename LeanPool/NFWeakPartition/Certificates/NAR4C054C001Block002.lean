/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C054C001Part003Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C054C001Part003`. -/


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
noncomputable def nb054_split_alpha_0000 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_030), (nb054_alpha_dummy_033 x y)),
        ((nb054_alpha_dummy_029), (nb054_alpha_dummy_032 x y)),
        ((nb054_alpha_dummy_028), (nb054_alpha_dummy_031 x y)),
        ((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
        ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
        ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
        ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
        ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
        ((nb054_alpha_dummy_020), (nb054_alpha_dummy_021 x y)),
        ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb054_alpha_dummy_028))
            (syn_cun (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb054_alpha_dummy_032 x y))
            (Class.cv (nb054_alpha_dummy_033 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_031 x y))
            (syn_cun (Class.cv (nb054_alpha_dummy_032 x y))
              (Class.cv (nb054_alpha_dummy_033 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb054_alpha_dummy_030), (nb054_alpha_dummy_033 x y)),
          ((nb054_alpha_dummy_029), (nb054_alpha_dummy_032 x y)),
          ((nb054_alpha_dummy_028), (nb054_alpha_dummy_031 x y)),
          ((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
          ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
          ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
          ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
          ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
          ((nb054_alpha_dummy_020), (nb054_alpha_dummy_021 x y)),
          ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
          ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C054C001Part004`. -/


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
noncomputable def nb054_split_alpha_0001 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
        ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
        ((nb054_alpha_dummy_020), (nb054_alpha_dummy_021 x y)),
        ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.classEq (Class.cv (nb054_alpha_dummy_014))
        (syn_cphi (Class.cv (nb054_alpha_dummy_015))))
      (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y))
        (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv)
          (by decide)) (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0020) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0021 x y) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0020) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0021 x y) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb054_alpha_dummy_015))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb054_alpha_dummy_017 x y))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0024) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0025 x y) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0024) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0025 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb054_support_mem_0022) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb054_alpha_dummy_030),
                                        (nb054_alpha_dummy_033 x y)), ((nb054_alpha_dummy_029),
                                        (nb054_alpha_dummy_032 x y)), ((nb054_alpha_dummy_028),
                                        (nb054_alpha_dummy_031 x y)), ((nb054_alpha_dummy_026),
                                        (nb054_alpha_dummy_027 x y)), ((nb054_alpha_dummy_022),
                                        (nb054_alpha_dummy_024 x y)), ((nb054_alpha_dummy_023),
                                        (nb054_alpha_dummy_025 x y)), ((nb054_alpha_dummy_015),
                                        (nb054_alpha_dummy_017 x y)), ((nb054_alpha_dummy_014),
                                        (nb054_alpha_dummy_016 x y)), ((nb054_alpha_dummy_020),
                                        (nb054_alpha_dummy_021 x y)), ((nb054_alpha_dummy_018),
                                        (nb054_alpha_dummy_019 x y)), ((nb054_alpha_dummy_007),
                                        (nb054_alpha_dummy_009 x y)), ((nb054_alpha_dummy_006),
                                        (nb054_alpha_dummy_008 x y)), ((nb054_alpha_dummy_012),
                                        (nb054_alpha_dummy_013 x y)), ((nb054_alpha_dummy_010),
                                        (nb054_alpha_dummy_011 x y)), ((nb054_alpha_dummy_002),
                                        (nb054_alpha_dummy_003 x y)),
                                      ((nb054_alpha_dummy_001), y),
                                      ((nb054_alpha_dummy_000), x), ((nb054_alpha_dummy_004),
                                        (nb054_alpha_dummy_005 x y))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb054_split_alpha_0000 x y))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
                          ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
                          ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
                          ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                          ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                          ((nb054_alpha_dummy_020), (nb054_alpha_dummy_021 x y)),
                          ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                          ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0022) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
                          ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
                          ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
                          ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                          ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                          ((nb054_alpha_dummy_020), (nb054_alpha_dummy_021 x y)),
                          ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                          ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb054_split_alpha_0002 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_030), (nb054_alpha_dummy_033 x y)),
        ((nb054_alpha_dummy_029), (nb054_alpha_dummy_032 x y)),
        ((nb054_alpha_dummy_028), (nb054_alpha_dummy_031 x y)),
        ((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
        ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
        ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
        ((nb054_alpha_dummy_048), (nb054_alpha_dummy_049 x y)),
        ((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
        ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
        ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
        ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
        ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb054_alpha_dummy_028))
            (syn_cun (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb054_alpha_dummy_032 x y))
            (Class.cv (nb054_alpha_dummy_033 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_031 x y))
            (syn_cun (Class.cv (nb054_alpha_dummy_032 x y))
              (Class.cv (nb054_alpha_dummy_033 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0028) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0029 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0027 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0032) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0033 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0031 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb054_alpha_dummy_030), (nb054_alpha_dummy_033 x y)),
          ((nb054_alpha_dummy_029), (nb054_alpha_dummy_032 x y)),
          ((nb054_alpha_dummy_028), (nb054_alpha_dummy_031 x y)),
          ((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
          ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
          ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
          ((nb054_alpha_dummy_048), (nb054_alpha_dummy_049 x y)),
          ((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
          ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
          ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
          ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
          ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
          ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0036) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0037 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0034) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0035 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0040) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0041 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0038) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0039 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb054_split_alpha_0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
        ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
        ((nb054_alpha_dummy_048), (nb054_alpha_dummy_049 x y)),
        ((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
        ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
        ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
        ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
        ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_022))
          (Class.cv (nb054_alpha_dummy_015))) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_023))
            (syn_cif (Wff.classMem (Class.cv (nb054_alpha_dummy_022)) (syn_cnnc))
              (syn_cplc (Class.cv (nb054_alpha_dummy_022)) (syn_c1c))
              (Class.cv (nb054_alpha_dummy_022))))))
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_024 x y))
          (Class.cv (nb054_alpha_dummy_017 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_025 x y))
            (syn_cif (Wff.classMem (Class.cv (nb054_alpha_dummy_024 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb054_alpha_dummy_024 x y)) (syn_c1c))
              (Class.cv (nb054_alpha_dummy_024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0020) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0021 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0020) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0021 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0058) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0059 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0056) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0057 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb054_alpha_dummy_015))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb054_alpha_dummy_017 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0024) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0025 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb054_support_mem_0024) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb054_support_mem_0025 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0022) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb054_alpha_dummy_030), (nb054_alpha_dummy_033 x y)),
                                  ((nb054_alpha_dummy_029), (nb054_alpha_dummy_032 x y)),
                                  ((nb054_alpha_dummy_028), (nb054_alpha_dummy_031 x y)),
                                  ((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
                                  ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
                                  ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
                                  ((nb054_alpha_dummy_048), (nb054_alpha_dummy_049 x y)),
                                  ((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
                                  ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                                  ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                                  ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
                                  ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                                  ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                                  ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                                  ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                                  ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                                  ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                                  ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                                  ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb054_split_alpha_0002 x y))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
                      ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
                      ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
                      ((nb054_alpha_dummy_048), (nb054_alpha_dummy_049 x y)),
                      ((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
                      ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                      ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                      ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
                      ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                      ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                      ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                      ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                      ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                      ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                      ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                      ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0022) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0022) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0023 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb054_alpha_dummy_026), (nb054_alpha_dummy_027 x y)),
                      ((nb054_alpha_dummy_022), (nb054_alpha_dummy_024 x y)),
                      ((nb054_alpha_dummy_023), (nb054_alpha_dummy_025 x y)),
                      ((nb054_alpha_dummy_048), (nb054_alpha_dummy_049 x y)),
                      ((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
                      ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                      ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                      ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
                      ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                      ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                      ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                      ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                      ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                      ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                      ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                      ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C054C001Part005`. -/


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
noncomputable def nb054_variable_occurrence_0 (x y : Var) :
    TAlphaClass
      [(nb054_alpha_dummy_015, (nb054_alpha_dummy_017 x y)),
        (nb054_alpha_dummy_014, (nb054_alpha_dummy_016 x y)),
        (nb054_alpha_dummy_044, (nb054_alpha_dummy_045 x y)),
        (nb054_alpha_dummy_018, (nb054_alpha_dummy_019 x y)),
        (nb054_alpha_dummy_007, (nb054_alpha_dummy_009 x y)),
        (nb054_alpha_dummy_006, (nb054_alpha_dummy_008 x y)),
        (nb054_alpha_dummy_012, (nb054_alpha_dummy_013 x y)),
        (nb054_alpha_dummy_010, (nb054_alpha_dummy_011 x y)),
        (nb054_alpha_dummy_002, (nb054_alpha_dummy_003 x y)), (nb054_alpha_dummy_001, y),
        (nb054_alpha_dummy_000, x), (nb054_alpha_dummy_004, (nb054_alpha_dummy_005 x y))]
      (Class.cv nb054_alpha_dummy_001) (Class.cv y) :=
  by
  have freshness0 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_015 :=
    by
    unfold nb054_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 1))
  have freshness1 : y ≠ (nb054_alpha_dummy_017 x y) :=
    by
    unfold nb054_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 1))
  have freshness2 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_014 :=
    by
    unfold nb054_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 0))
  have freshness3 : y ≠ (nb054_alpha_dummy_016 x y) :=
    by
    unfold nb054_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 0))
  have freshness4 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_044 :=
    by
    unfold nb054_alpha_dummy_044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0054) 0))
  have freshness5 : y ≠ (nb054_alpha_dummy_045 x y) :=
    by
    unfold nb054_alpha_dummy_045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0055 x y) 0))
  have freshness6 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_018 :=
    by
    unfold nb054_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0051) 0))
  have freshness7 : y ≠ (nb054_alpha_dummy_019 x y) :=
    by
    unfold nb054_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0053 x y) 0))
  have freshness8 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_007 :=
    by
    unfold nb054_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 1))
  have freshness9 : y ≠ (nb054_alpha_dummy_009 x y) :=
    by
    unfold nb054_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 1))
  have freshness10 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_006 :=
    by
    unfold nb054_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 0))
  have freshness11 : y ≠ (nb054_alpha_dummy_008 x y) :=
    by
    unfold nb054_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 0))
  have freshness12 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_012 :=
    by
    unfold nb054_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0048) 0))
  have freshness13 : y ≠ (nb054_alpha_dummy_013 x y) :=
    by
    unfold nb054_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0049 x y) 0))
  have freshness14 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_010 :=
    by
    unfold nb054_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0045) 0))
  have freshness15 : y ≠ (nb054_alpha_dummy_011 x y) :=
    by
    unfold nb054_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0047 x y) 0))
  have freshness16 : nb054_alpha_dummy_001 ≠ nb054_alpha_dummy_002 :=
    by
    unfold nb054_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0042) 0))
  have freshness17 : y ≠ (nb054_alpha_dummy_003 x y) :=
    by
    unfold nb054_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0043 x y) 0))
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
noncomputable def nb054_variable_occurrence_1 (x y : Var) (dv_x_y : x ≠ y) :
    TAlphaClass
      [(nb054_alpha_dummy_015, (nb054_alpha_dummy_017 x y)),
        (nb054_alpha_dummy_014, (nb054_alpha_dummy_016 x y)),
        (nb054_alpha_dummy_020, (nb054_alpha_dummy_021 x y)),
        (nb054_alpha_dummy_018, (nb054_alpha_dummy_019 x y)),
        (nb054_alpha_dummy_007, (nb054_alpha_dummy_009 x y)),
        (nb054_alpha_dummy_006, (nb054_alpha_dummy_008 x y)),
        (nb054_alpha_dummy_012, (nb054_alpha_dummy_013 x y)),
        (nb054_alpha_dummy_010, (nb054_alpha_dummy_011 x y)),
        (nb054_alpha_dummy_002, (nb054_alpha_dummy_003 x y)), (nb054_alpha_dummy_001, y),
        (nb054_alpha_dummy_000, x), (nb054_alpha_dummy_004, (nb054_alpha_dummy_005 x y))]
      (Class.cv nb054_alpha_dummy_000) (Class.cv x) :=
  by
  have freshness0 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_015 :=
    by
    unfold nb054_alpha_dummy_015
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 1))
  have freshness1 : x ≠ (nb054_alpha_dummy_017 x y) :=
    by
    unfold nb054_alpha_dummy_017
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 1))
  have freshness2 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_014 :=
    by
    unfold nb054_alpha_dummy_014
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 0))
  have freshness3 : x ≠ (nb054_alpha_dummy_016 x y) :=
    by
    unfold nb054_alpha_dummy_016
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 0))
  have freshness4 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_020 :=
    by
    unfold nb054_alpha_dummy_020
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0018) 0))
  have freshness5 : x ≠ (nb054_alpha_dummy_021 x y) :=
    by
    unfold nb054_alpha_dummy_021
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0019 x y) 0))
  have freshness6 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_018 :=
    by
    unfold nb054_alpha_dummy_018
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0015) 0))
  have freshness7 : x ≠ (nb054_alpha_dummy_019 x y) :=
    by
    unfold nb054_alpha_dummy_019
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0017 x y) 0))
  have freshness8 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_007 :=
    by
    unfold nb054_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 1))
  have freshness9 : x ≠ (nb054_alpha_dummy_009 x y) :=
    by
    unfold nb054_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 1))
  have freshness10 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_006 :=
    by
    unfold nb054_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 0))
  have freshness11 : x ≠ (nb054_alpha_dummy_008 x y) :=
    by
    unfold nb054_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 0))
  have freshness12 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_012 :=
    by
    unfold nb054_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0012) 0))
  have freshness13 : x ≠ (nb054_alpha_dummy_013 x y) :=
    by
    unfold nb054_alpha_dummy_013
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0013 x y) 0))
  have freshness14 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_010 :=
    by
    unfold nb054_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0009) 0))
  have freshness15 : x ≠ (nb054_alpha_dummy_011 x y) :=
    by
    unfold nb054_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0011 x y) 0))
  have freshness16 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_002 :=
    by
    unfold nb054_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0006) 0))
  have freshness17 : x ≠ (nb054_alpha_dummy_003 x y) :=
    by
    unfold nb054_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0007 x y) 0))
  have freshness18 : nb054_alpha_dummy_000 ≠ nb054_alpha_dummy_001 :=
    by
    unfold nb054_alpha_dummy_000 nb054_alpha_dummy_001
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
noncomputable def nb054_split_alpha_0004 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
        ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_044))
          (Class.cab (nb054_alpha_dummy_014)
            (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb054_alpha_dummy_014))
                (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb054_alpha_dummy_044))
            (Class.cab (nb054_alpha_dummy_014)
              (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_014))
                  (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_045 x y))
          (Class.cab (nb054_alpha_dummy_016 x y)
            (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y))
                (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb054_alpha_dummy_045 x y))
            (Class.cab (nb054_alpha_dummy_016 x y)
              (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y))
                  (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (nb054_variable_occurrence_0 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                      ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb054_split_alpha_0003 x y)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb054_split_alpha_0003 x y)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
                          ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                          ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                          ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
                          ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                          ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (nb054_variable_occurrence_0 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                        ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb054_split_alpha_0003 x y)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb054_split_alpha_0003 x y)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb054_alpha_dummy_046), (nb054_alpha_dummy_047 x y)),
                            ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
                            ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
                            ((nb054_alpha_dummy_044), (nb054_alpha_dummy_045 x y)),
                            ((nb054_alpha_dummy_018), (nb054_alpha_dummy_019 x y)),
                            ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                            ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                            ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                            ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                            ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                            ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                            ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb054_split_alpha_0005 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_058), (nb054_alpha_dummy_061 x y)),
        ((nb054_alpha_dummy_057), (nb054_alpha_dummy_060 x y)),
        ((nb054_alpha_dummy_056), (nb054_alpha_dummy_059 x y)),
        ((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
        ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
        ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb054_alpha_dummy_056))
            (syn_cun (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb054_alpha_dummy_060 x y))
            (Class.cv (nb054_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_059 x y))
            (syn_cun (Class.cv (nb054_alpha_dummy_060 x y))
              (Class.cv (nb054_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb054_alpha_dummy_058), (nb054_alpha_dummy_061 x y)),
          ((nb054_alpha_dummy_057), (nb054_alpha_dummy_060 x y)),
          ((nb054_alpha_dummy_056), (nb054_alpha_dummy_059 x y)),
          ((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
          ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
          ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
          ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb054_split_alpha_0006 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_007))
          (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))))
        (Wff.neg (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
            (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_009 x y))
          (syn_cop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
            (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb054_variable_occurrence_1 x y dv_x_y))
                            (nb054_split_alpha_0001 x y)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb054_variable_occurrence_1 x y dv_x_y))
                            (nb054_split_alpha_0001 x y)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb054_split_alpha_0004 x y)))))))))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cop (Class.cv (nb054_alpha_dummy_000))
                    (Class.cv (nb054_alpha_dummy_001)))).fv ∪
                ((Class.cv (nb054_alpha_dummy_002))).fv) (by decide)) (freshVar_injective
              (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb054_alpha_dummy_003 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0060) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0061 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0060) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0061 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb054_alpha_dummy_007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb054_alpha_dummy_009 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb054_support_mem_0064) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb054_support_mem_0065 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0064) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0065 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0062) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0063 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb054_alpha_dummy_058),
        (nb054_alpha_dummy_061 x y)), ((nb054_alpha_dummy_057), (nb054_alpha_dummy_060 x y)),
        ((nb054_alpha_dummy_056), (nb054_alpha_dummy_059 x y)), ((nb054_alpha_dummy_054),
        (nb054_alpha_dummy_055 x y)), ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
        ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)), ((nb054_alpha_dummy_007),
        (nb054_alpha_dummy_009 x y)), ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)), ((nb054_alpha_dummy_010),
        (nb054_alpha_dummy_011 x y)), ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x), ((nb054_alpha_dummy_004),
        (nb054_alpha_dummy_005 x y))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb054_split_alpha_0005 x y))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
                              ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
                              ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
                              ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                              ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                              ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                              ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                              ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                              ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                              ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
                              ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
                              ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
                              ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                              ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                              ((nb054_alpha_dummy_012), (nb054_alpha_dummy_013 x y)),
                              ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                              ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                              ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                              ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb054_split_alpha_0007 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_058), (nb054_alpha_dummy_061 x y)),
        ((nb054_alpha_dummy_057), (nb054_alpha_dummy_060 x y)),
        ((nb054_alpha_dummy_056), (nb054_alpha_dummy_059 x y)),
        ((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
        ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
        ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
        ((nb054_alpha_dummy_076), (nb054_alpha_dummy_077 x y)),
        ((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb054_alpha_dummy_056))
            (syn_cun (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb054_alpha_dummy_060 x y))
            (Class.cv (nb054_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_059 x y))
            (syn_cun (Class.cv (nb054_alpha_dummy_060 x y))
              (Class.cv (nb054_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0069 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0067 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0072) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0070) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0071 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb054_alpha_dummy_058), (nb054_alpha_dummy_061 x y)),
          ((nb054_alpha_dummy_057), (nb054_alpha_dummy_060 x y)),
          ((nb054_alpha_dummy_056), (nb054_alpha_dummy_059 x y)),
          ((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
          ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
          ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
          ((nb054_alpha_dummy_076), (nb054_alpha_dummy_077 x y)),
          ((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
          ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
          ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
          ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
          ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0077 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0075 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0080) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0081 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0078) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0079 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C054C001Part006`. -/


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
noncomputable def nb054_split_alpha_0008 (x : Var) (y : Var) :
    TAlphaClass
      [((nb054_alpha_dummy_076), (nb054_alpha_dummy_077 x y)),
        ((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
        ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Class.cab (nb054_alpha_dummy_051)
        (syn_wrex (nb054_alpha_dummy_050) (Class.cv (nb054_alpha_dummy_007))
          (Wff.classEq (Class.cv (nb054_alpha_dummy_051))
            (syn_cif (Wff.classMem (Class.cv (nb054_alpha_dummy_050)) (syn_cnnc))
              (syn_cplc (Class.cv (nb054_alpha_dummy_050)) (syn_c1c))
              (Class.cv (nb054_alpha_dummy_050))))))
      (Class.cab (nb054_alpha_dummy_053 x y)
        (syn_wrex (nb054_alpha_dummy_052 x y) (Class.cv (nb054_alpha_dummy_009 x y))
          (Wff.classEq (Class.cv (nb054_alpha_dummy_053 x y))
            (syn_cif (Wff.classMem (Class.cv (nb054_alpha_dummy_052 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb054_alpha_dummy_052 x y)) (syn_c1c))
              (Class.cv (nb054_alpha_dummy_052 x y)))))) :=
  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0060) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0061 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0060) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0061 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0090) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0091 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0089 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb054_alpha_dummy_007))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb054_alpha_dummy_009 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb054_support_mem_0064) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb054_support_mem_0065 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0064) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0065 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0062) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb054_alpha_dummy_058), (nb054_alpha_dummy_061 x y)),
                                    ((nb054_alpha_dummy_057), (nb054_alpha_dummy_060 x y)),
                                    ((nb054_alpha_dummy_056), (nb054_alpha_dummy_059 x y)),
                                    ((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
                                    ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
                                    ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
                                    ((nb054_alpha_dummy_076), (nb054_alpha_dummy_077 x y)),
                                    ((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
                                    ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                                    ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                                    ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
                                    ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                                    ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                                    ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                                    ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb054_split_alpha_0007 x y))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
                        ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
                        ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
                        ((nb054_alpha_dummy_076), (nb054_alpha_dummy_077 x y)),
                        ((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
                        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                        ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
                        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0062) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0062) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0063 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb054_alpha_dummy_054), (nb054_alpha_dummy_055 x y)),
                        ((nb054_alpha_dummy_050), (nb054_alpha_dummy_052 x y)),
                        ((nb054_alpha_dummy_051), (nb054_alpha_dummy_053 x y)),
                        ((nb054_alpha_dummy_076), (nb054_alpha_dummy_077 x y)),
                        ((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
                        ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                        ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                        ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
                        ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def nb054_variable_occurrence_2 (x y : Var) :
    TAlphaClass
      [(nb054_alpha_dummy_007, (nb054_alpha_dummy_009 x y)),
        (nb054_alpha_dummy_006, (nb054_alpha_dummy_008 x y)),
        (nb054_alpha_dummy_072, (nb054_alpha_dummy_073 x y)),
        (nb054_alpha_dummy_010, (nb054_alpha_dummy_011 x y)),
        (nb054_alpha_dummy_002, (nb054_alpha_dummy_003 x y)), (nb054_alpha_dummy_001, y),
        (nb054_alpha_dummy_000, x), (nb054_alpha_dummy_004, (nb054_alpha_dummy_005 x y))]
      (Class.cv nb054_alpha_dummy_002) (Class.cv (nb054_alpha_dummy_003 x y)) :=
  by
  have freshness0 : nb054_alpha_dummy_002 ≠ nb054_alpha_dummy_007 :=
    by
    unfold nb054_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 1))
  have freshness1 : (nb054_alpha_dummy_003 x y) ≠ (nb054_alpha_dummy_009 x y) :=
    by
    unfold nb054_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 1))
  have freshness2 : nb054_alpha_dummy_002 ≠ nb054_alpha_dummy_006 :=
    by
    unfold nb054_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 0))
  have freshness3 : (nb054_alpha_dummy_003 x y) ≠ (nb054_alpha_dummy_008 x y) :=
    by
    unfold nb054_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 0))
  have freshness4 : nb054_alpha_dummy_002 ≠ nb054_alpha_dummy_072 :=
    by
    unfold nb054_alpha_dummy_072
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0086) 0))
  have freshness5 : (nb054_alpha_dummy_003 x y) ≠ (nb054_alpha_dummy_073 x y) :=
    by
    unfold nb054_alpha_dummy_073
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0087 x y) 0))
  have freshness6 : nb054_alpha_dummy_002 ≠ nb054_alpha_dummy_010 :=
    by
    unfold nb054_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0083) 0))
  have freshness7 : (nb054_alpha_dummy_003 x y) ≠ (nb054_alpha_dummy_011 x y) :=
    by
    unfold nb054_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0085 x y) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

@[expose]
noncomputable def nb054_split_alpha_0009 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_010)) (syn_ccompl
            (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007)
                (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb054_alpha_dummy_010)) (syn_ccompl
              (Class.cab (nb054_alpha_dummy_006)
                (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002))
                  (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
                    (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb054_alpha_dummy_011 x y)) (syn_ccompl
            (Class.cab (nb054_alpha_dummy_008 x y)
              (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb054_alpha_dummy_011 x y)) (syn_ccompl
              (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y)
                  (Class.cv (nb054_alpha_dummy_003 x y))
                  (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                    (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb054_split_alpha_0006 x y dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb054_split_alpha_0006 x y dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb054_variable_occurrence_2 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((syn_cop (Class.cv (nb054_alpha_dummy_000))
                                    (Class.cv (nb054_alpha_dummy_001)))).fv ∪
                                ((Class.cv (nb054_alpha_dummy_002))).fv) (by decide))
                            (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb054_alpha_dummy_003 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb054_split_alpha_0008 x y)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb054_split_alpha_0008 x y))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
                                    ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                                    ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                                    ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
                                    ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                                    ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                                    ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                                    ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (nb054_variable_occurrence_2 x y)) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((syn_cop (Class.cv (nb054_alpha_dummy_000))
                                    (Class.cv (nb054_alpha_dummy_001)))).fv ∪
                                ((Class.cv (nb054_alpha_dummy_002))).fv) (by decide))
                            (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                ((Class.cv (nb054_alpha_dummy_003 x y))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb054_split_alpha_0008 x y)) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb054_split_alpha_0008 x y))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb054_alpha_dummy_074), (nb054_alpha_dummy_075 x y)),
                                    ((nb054_alpha_dummy_007), (nb054_alpha_dummy_009 x y)),
                                    ((nb054_alpha_dummy_006), (nb054_alpha_dummy_008 x y)),
                                    ((nb054_alpha_dummy_072), (nb054_alpha_dummy_073 x y)),
                                    ((nb054_alpha_dummy_010), (nb054_alpha_dummy_011 x y)),
                                    ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                                    ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                                    ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

@[expose]
noncomputable def nb054_split_alpha_0010 (x : Var) (y : Var) :
    TAlphaWff
      [((nb054_alpha_dummy_078), (nb054_alpha_dummy_079 x y)),
        ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
        ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
        ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
        ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
        ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb054_alpha_dummy_014))
            (syn_cun (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb054_alpha_dummy_017 x y))
            (Class.cv (nb054_alpha_dummy_079 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y))
            (syn_cun (Class.cv (nb054_alpha_dummy_017 x y))
              (Class.cv (nb054_alpha_dummy_079 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                                  ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
                              (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                                  ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
                              (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb054_alpha_dummy_078), (nb054_alpha_dummy_079 x y)),
          ((nb054_alpha_dummy_015), (nb054_alpha_dummy_017 x y)),
          ((nb054_alpha_dummy_014), (nb054_alpha_dummy_016 x y)),
          ((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                  ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
              (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb054_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb054_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nominal_df_addcfn (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_caddcfn) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cplc (.cv x) (.cv y)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0004) 0))) (Ne.symm
                        (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0005 x y) 0)))
                      (TAlphaVar.there (Ne.symm
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0002) 0))) (Ne.symm
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0003 x y) 0)))
                        (TAlphaVar.there (Ne.symm
                            (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0000) 0)))
                          (Ne.symm (Nat.ne_of_lt
                              (mem_lt_freshVar (nb054_support_mem_0001 x y) 0)))
                          (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb054_split_alpha_0009 x y dv_x_y)))))
                (TAlphaWff.conj (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0006) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0007 x y) 0))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.refl_of_closed
                        [((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0042) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0043 x y) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb054_alpha_dummy_002), (nb054_alpha_dummy_003 x y)),
                          ((nb054_alpha_dummy_001), y), ((nb054_alpha_dummy_000), x),
                          ((nb054_alpha_dummy_004), (nb054_alpha_dummy_005 x y))]
                        (syn_cvv) (by simp only [fv_syn_cvv]))))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb054_support_mem_0014) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb054_support_mem_0016 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0014) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb054_support_mem_0016 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0006) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0007 x y) 0))
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide))
                                      dv_x_y (TAlphaVar.here _ _ _))))))) (TAlphaWff.ex
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0050) 2))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb054_support_mem_0052 x y) 2))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb054_support_mem_0050) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb054_support_mem_0052 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0052 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0042) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb054_support_mem_0043 x y) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.neg (nb054_split_alpha_0010 x y))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
