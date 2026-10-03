/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NA50WN14DBlock001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NA50WN14DPart010`. -/


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
noncomputable def nb050_split_alpha_0000 (x : Var) (y : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)),
        ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)),
        ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)),
        ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
        ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
        ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
        ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
        ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
        ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
        ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
        ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb050_alpha_dummy_017 x A B))
            (syn_cun (Class.cv (nb050_alpha_dummy_018 x A B))
              (Class.cv (nb050_alpha_dummy_019 x A B))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb050_alpha_dummy_020 x y))
            (syn_cun (Class.cv (nb050_alpha_dummy_021 x y))
              (Class.cv (nb050_alpha_dummy_022 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0019 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0020 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0017 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0018 x y) 0)) (TAlphaVar.there
                              (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0023 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0024 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0021 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0022 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0019 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0020 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0017 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0018 x y) 0)) (TAlphaVar.there
                              (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0023 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0024 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0021 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0022 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)),
          ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)),
          ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)),
          ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
          ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
          ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
          ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
          ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
          ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
          ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
          ((nb050_alpha_dummy_000 x A B), y), (x, x),
          ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0027 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0028 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0025 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0026 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0027 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0028 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0025 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0026 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0031 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0032 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0029 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0030 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0031 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0032 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0029 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0030 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart013`. -/


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
noncomputable def nb050_split_alpha_0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
        ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
        ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
        ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
        ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (Wff.neg (Wff.imp (Wff.classMem (Class.cv (nb050_alpha_dummy_004 x A B)) (Class.cv x))
          (Wff.neg (Wff.classEq (Class.cv (nb050_alpha_dummy_003 x A B))
              (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))))))
      (Wff.neg (Wff.imp (Wff.classMem (Class.cv (nb050_alpha_dummy_006 x y)) (Class.cv x))
          (Wff.neg (Wff.classEq (Class.cv (nb050_alpha_dummy_005 x y))
              (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y))))))) :=
  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
      (TAlphaClass.refl_of_reflOn [((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
          ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
          ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
          ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
          ((nb050_alpha_dummy_000 x A B), y), (x, x),
          ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
        (Class.cv x) (nb050_wpp_refl_0000 x y A B dv_x_y))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective
            (((Class.cv x)).fv ∪ ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) (by decide))
          (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0011 x A B) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0012 x y) 0))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0011 x A B) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0012 x y) 1))
                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb050_alpha_dummy_004 x A B))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb050_alpha_dummy_006 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0015 x A B) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0016 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0015 x A B) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0016 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0014 x y) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb050_alpha_dummy_019 x A B),
        (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B),
        (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B),
        (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B),
        (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B),
        (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B),
        (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_004 x A B),
        (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B),
        (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B),
        (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B),
        (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x),
                                        ((nb050_alpha_dummy_001 x A B),
        (nb050_alpha_dummy_002 x y A B))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb050_split_alpha_0000 x y A B))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
                            ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
                            ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
                            ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
                            ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
                            ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
                            ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
                            ((nb050_alpha_dummy_000 x A B), y), (x, x),
                            ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
                            ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
                            ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
                            ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
                            ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
                            ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)),
                            ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
                            ((nb050_alpha_dummy_000 x A B), y), (x, x),
                            ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart018`. -/


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
noncomputable def nb050_split_alpha_0002 (x : Var) (y : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)),
        ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)),
        ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)),
        ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
        ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
        ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
        ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
        ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
        ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
        ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
        ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
        ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
        ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb050_alpha_dummy_018 x A B))
            (Class.cv (nb050_alpha_dummy_019 x A B))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb050_alpha_dummy_017 x A B))
            (syn_cun (Class.cv (nb050_alpha_dummy_018 x A B))
              (Class.cv (nb050_alpha_dummy_019 x A B))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb050_alpha_dummy_021 x y))
            (Class.cv (nb050_alpha_dummy_022 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb050_alpha_dummy_020 x y))
            (syn_cun (Class.cv (nb050_alpha_dummy_021 x y))
              (Class.cv (nb050_alpha_dummy_022 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0019 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0020 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0017 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0018 x y) 0)) (TAlphaVar.there
                              (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0023 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0024 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0021 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0022 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0019 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0020 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0017 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0018 x y) 0)) (TAlphaVar.there
                              (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0023 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0024 x y) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0021 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0022 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)),
          ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)),
          ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)),
          ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
          ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
          ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
          ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
          ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
          ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
          ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
          ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
          ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
          ((nb050_alpha_dummy_000 x A B), y), (x, x),
          ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0027 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0028 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0025 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0026 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0027 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0028 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0025 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0026 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_011 x A B))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb050_alpha_dummy_013 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0031 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0032 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0029 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0030 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0031 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0032 x y) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0029 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0030 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart021`. -/


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
noncomputable def nb050_split_alpha_0003 (x : Var) (y : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
        ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
        ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
        ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
        ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
        ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
        ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (Wff.imp (Wff.classMem (Class.cv (nb050_alpha_dummy_037 x A B))
          (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B)))) (Wff.neg
          (Wff.classMem (Class.cv (nb050_alpha_dummy_037 x A B))
            (syn_cphi (Class.cv (nb050_alpha_dummy_004 x A B))))))
      (Wff.imp (Wff.classMem (Class.cv (nb050_alpha_dummy_038 x y))
          (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (nb050_alpha_dummy_038 x y))
            (syn_cphi (Class.cv (nb050_alpha_dummy_006 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0011 x A B) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0012 x y) 0))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0011 x A B) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0012 x y) 1))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0041 x A B) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0042 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0039 x A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0040 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb050_alpha_dummy_004 x A B))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb050_alpha_dummy_006 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0015 x A B) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0016 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0015 x A B) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0016 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0014 x y) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb050_alpha_dummy_019 x A B),
        (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B),
        (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B),
        (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B),
        (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B),
        (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B),
        (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_037 x A B),
        (nb050_alpha_dummy_038 x y)), ((nb050_alpha_dummy_035 x A B),
        (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B),
        (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B),
        (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B),
        (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B),
        (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x),
                                        ((nb050_alpha_dummy_001 x A B),
        (nb050_alpha_dummy_002 x y A B))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb050_split_alpha_0002 x y A B))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
                            ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
                            ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
                            ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
                            ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
                            ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
                            ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
                            ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
                            ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
                            ((nb050_alpha_dummy_000 x A B), y), (x, x),
                            ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
                            ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
                            ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
                            ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
                            ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
                            ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
                            ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
                            ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
                            ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
                            ((nb050_alpha_dummy_000 x A B), y), (x, x),
                            ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0011 x A B) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0012 x y) 0))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0011 x A B) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0012 x y) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0041 x A B) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0042 x y) 0))
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb050_support_mem_0039 x A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0040 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb050_alpha_dummy_004 x A B))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb050_alpha_dummy_006 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0015 x A B) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0016 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0015 x A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0016 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb050_support_mem_0014 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb050_alpha_dummy_019 x A B),
        (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B),
        (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B),
        (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B),
        (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B),
        (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B),
        (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_037 x A B),
        (nb050_alpha_dummy_038 x y)), ((nb050_alpha_dummy_035 x A B),
        (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B),
        (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B),
        (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B),
        (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B),
        (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb050_split_alpha_0002 x y A B))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
                              ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
                              ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
                              ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
                              ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
                              ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
                              ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
                              ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
                              ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
                              ((nb050_alpha_dummy_000 x A B), y), (x, x),
                              ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb050_support_mem_0013 x A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0014 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)),
                              ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)),
                              ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)),
                              ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)),
                              ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)),
                              ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)),
                              ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)),
                              ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)),
                              ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)),
                              ((nb050_alpha_dummy_000 x A B), y), (x, x),
                              ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart024`. -/


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
noncomputable def nb050_split_alpha_0004 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (Wff.classEq (Class.cv (nb050_alpha_dummy_001 x A B))
        (syn_cop (Class.cv x) (Class.cv (nb050_alpha_dummy_000 x A B))))
      (Wff.classEq (Class.cv (nb050_alpha_dummy_002 x y A B))
        (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0002 x A B) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0003 x y A B) 0)))
        (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0000 x A B) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0001 x y A B) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (nb050_split_alpha_0001 x y A B dv_x_y))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (nb050_split_alpha_0001 x y A B dv_x_y))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb050_support_mem_0033 x A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb050_support_mem_0033 x A B) 0))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb050_support_mem_0035 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0037 x A B) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0038 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0034 x A B) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0036 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv x)).fv ∪
                                    ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb050_split_alpha_0003 x y A B))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb050_alpha_dummy_035 x A B),
        (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B),
        (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B),
        (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B),
        (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B),
        (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x),
                                        ((nb050_alpha_dummy_001 x A B),
        (nb050_alpha_dummy_002 x y A B))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb050_support_mem_0033 x A B) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0035 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb050_support_mem_0033 x A B) 0))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb050_support_mem_0035 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0037 x A B) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb050_support_mem_0038 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0034 x A B) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb050_support_mem_0036 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv x)).fv ∪
                                    ((Class.cv (nb050_alpha_dummy_000 x A B))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb050_split_alpha_0003 x y A B))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb050_alpha_dummy_035 x A B),
        (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B),
        (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B),
        (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B),
        (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B),
        (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x),
                                        ((nb050_alpha_dummy_001 x A B),
        (nb050_alpha_dummy_002 x y A B))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart025`. -/


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

theorem nb050_focused_notmem_0000 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ A.fv :=
  by
  change freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb050_wpp_notmem_0110 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ ((Wff.classMem (Class.cv x) A)).fv := by
  simpa only [nb050_alpha_dummy_000, fv_wff_classMem, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0010 x A B) 0)))
      (nb050_focused_notmem_0000 x A B))

theorem nb050_wpp_notmem_0111 (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) : y ∉ ((Wff.classMem (Class.cv x) A)).fv := by
  simp only [fv_wff_classMem, Finset.mem_union, fv_class_cv, (Ne.symm dv_x_y),
    Finset.mem_singleton, dv_A_y, or_false, not_false_eq_true]

theorem nb050_focused_notmem_0001 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv x) A)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B)).symm ▸
            (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv x) A).symm ▸
                (Finset.mem_union_right _ (hu))))))))

theorem nb050_wpp_notmem_0112 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉ ((Wff.classMem (Class.cv x) A)).fv := by
  simpa only [nb050_alpha_dummy_001, fv_wff_classMem, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0000 x A B) 0)))
      (nb050_focused_notmem_0001 x A B))

theorem nb050_focused_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _
          (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B)).symm ▸
            (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv x) A).symm ▸
                (Finset.mem_union_right _ (hu))))))))

theorem nb050_wpp_notmem_0113 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉ ((Wff.classMem (Class.cv x) A)).fv := by
  simpa only [nb050_alpha_dummy_002, fv_wff_classMem, Finset.mem_union, fv_class_cv,
    Finset.mem_singleton, not_or] using
    (And.intro (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb050_support_mem_0001 x y A B) 0)))
      (nb050_focused_notmem_0002 x y A B))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart026`. -/


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

theorem nb050_compact_envfresh_0008 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    TEnvFresh
      [((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      ((Wff.classMem (Class.cv x) A)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0110 x A B)
      (nb050_wpp_notmem_0111 x y A dv_A_y dv_x_y) (TEnvFresh.consSame x
        (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B)
          (nb050_wpp_notmem_0112 x A B) (nb050_wpp_notmem_0113 x y A B)
          (TEnvFresh.nil ((Wff.classMem (Class.cv x) A)).fv))))

@[expose]
noncomputable def nb050_wpp_refl_0008 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    TReflOn
      [((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      ((Wff.classMem (Class.cv x) A)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0008 x y A B dv_A_y dv_x_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart027`. -/


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

theorem nb050_focused_notmem_0003 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ B.fv :=
  by
  change freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb050_wpp_notmem_0114 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_000 x A B) ∉ (B).fv := by
  simp only [(nb050_focused_notmem_0003 x A B), not_false_eq_true]

theorem nb050_wpp_notmem_0115 (y : Var) (B : Class) (dv_B_y : y ∉ B.fv) : y ∉ (B).fv := by
  simp only [dv_B_y, not_false_eq_true]

theorem nb050_focused_notmem_0004 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({(nb050_alpha_dummy_000 x A B)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv x) A)
              (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                (Wff.classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B)).symm ▸
            (Finset.mem_union_right _
              (((fv_wff_classEq (Class.cv (nb050_alpha_dummy_000 x A B)) B).symm ▸
                (Finset.mem_union_right _ (hu))))))))

theorem nb050_wpp_notmem_0116 (x : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_001 x A B) ∉ (B).fv := by
  simp only [(nb050_focused_notmem_0004 x A B), not_false_eq_true]

theorem nb050_focused_notmem_0005 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _
          (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classEq (Class.cv y) B)).symm ▸
            (Finset.mem_union_right _ (((fv_wff_classEq (Class.cv y) B).symm ▸
                (Finset.mem_union_right _ (hu))))))))

theorem nb050_wpp_notmem_0117 (x : Var) (y : Var) (A : Class) (B : Class) :
    (nb050_alpha_dummy_002 x y A B) ∉ (B).fv := by
  simp only [(nb050_focused_notmem_0005 x y A B), not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart028`. -/


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

theorem nb050_compact_envfresh_0009 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_B_y : y ∉ B.fv) :
    TEnvFresh
      [((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (B).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0114 x A B)
      (nb050_wpp_notmem_0115 y B dv_B_y) (TEnvFresh.consSame x
        (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B)
          (nb050_wpp_notmem_0116 x A B) (nb050_wpp_notmem_0117 x y A B)
          (TEnvFresh.nil (B).fv))))

@[expose]
noncomputable def nb050_wpp_refl_0009 (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_B_y : y ∉ B.fv) :
    TReflOn
      [((nb050_alpha_dummy_000 x A B), y), (x, x),
        ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
      (B).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0009 x y A B dv_B_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NA50WN14DPart029`. -/


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
noncomputable def nominal_df_mpt (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cmpt x A B)
        (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb050_split_alpha_0004 x y A B dv_x_y) (TAlphaWff.conj
                (TAlphaWff.refl_of_reflOn [((nb050_alpha_dummy_000 x A B), y), (x, x),
                    ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                  (Wff.classMem (Class.cv x) A) (nb050_wpp_refl_0008 x y A B dv_A_y dv_x_y))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_reflOn [((nb050_alpha_dummy_000 x A B), y), (x, x),
                      ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))]
                    B (nb050_wpp_refl_0009 x y A B dv_B_y))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
