/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAPD051C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAPD051C001Part010`. -/


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
noncomputable def nb051_split_alpha_0000 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) :
    TAlphaWff
      [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)),
        ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)),
        ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)),
        ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
        ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)),
        ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)),
        ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051_alpha_dummy_017 x y A B C))
            (syn_cun (Class.cv (nb051_alpha_dummy_018 x y A B C))
              (Class.cv (nb051_alpha_dummy_019 x y A B C))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051_alpha_dummy_020 x y z))
            (syn_cun (Class.cv (nb051_alpha_dummy_021 x y z))
              (Class.cv (nb051_alpha_dummy_022 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)),
          ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)),
          ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)),
          ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
          ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)),
          ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)),
          ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
          ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
          ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)),
          ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
          ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
          ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (freshVar_injective
                (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part013`. -/


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
noncomputable def nb051_split_alpha_0001 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (Wff.imp (Wff.classMem (Class.cv (nb051_alpha_dummy_004 x y A B C))
          (syn_cop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C))
            (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))
      (Wff.imp (Wff.classMem (Class.cv (nb051_alpha_dummy_006 x y z))
          (syn_cop (Class.cv x) (Class.cv y))) (Wff.neg
          (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z))
            (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
      (TAlphaClass.refl_of_reflOn
        [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
          ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
          ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)),
          ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
          ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
          ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
        (syn_cop (Class.cv x) (Class.cv y)) (nb051_wpp_refl_0000 x y z A B C dv_x_z dv_y_z)))
    (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) (by decide))
            (freshVar_injective
              (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt
                        (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb051_alpha_dummy_006 x y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0023 x y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb051_alpha_dummy_019 x y A B C),
        (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C),
        (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C),
        (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C),
        (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C),
        (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C),
        (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_004 x y A B C),
        (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C),
        (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_009 x y A B C),
        (nb051_alpha_dummy_010 x y z)), ((nb051_alpha_dummy_007 x y A B C),
        (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg
                                      (nb051_split_alpha_0000 x y z A B C))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
                              ((nb051_alpha_dummy_011 x y A B C),
                                (nb051_alpha_dummy_013 x y z)),
                              ((nb051_alpha_dummy_012 x y A B C),
                                (nb051_alpha_dummy_014 x y z)),
                              ((nb051_alpha_dummy_004 x y A B C),
                                (nb051_alpha_dummy_006 x y z)),
                              ((nb051_alpha_dummy_003 x y A B C),
                                (nb051_alpha_dummy_005 x y z)),
                              ((nb051_alpha_dummy_009 x y A B C),
                                (nb051_alpha_dummy_010 x y z)),
                              ((nb051_alpha_dummy_007 x y A B C),
                                (nb051_alpha_dummy_008 x y z)),
                              ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                              ((nb051_alpha_dummy_001 x y A B C),
                                (nb051_alpha_dummy_002 x y z A B C))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
                              ((nb051_alpha_dummy_011 x y A B C),
                                (nb051_alpha_dummy_013 x y z)),
                              ((nb051_alpha_dummy_012 x y A B C),
                                (nb051_alpha_dummy_014 x y z)),
                              ((nb051_alpha_dummy_004 x y A B C),
                                (nb051_alpha_dummy_006 x y z)),
                              ((nb051_alpha_dummy_003 x y A B C),
                                (nb051_alpha_dummy_005 x y z)),
                              ((nb051_alpha_dummy_009 x y A B C),
                                (nb051_alpha_dummy_010 x y z)),
                              ((nb051_alpha_dummy_007 x y A B C),
                                (nb051_alpha_dummy_008 x y z)),
                              ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                              ((nb051_alpha_dummy_001 x y A B C),
                                (nb051_alpha_dummy_002 x y z A B C))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part018`. -/


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
noncomputable def nb051_split_alpha_0002 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) :
    TAlphaWff
      [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)),
        ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)),
        ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)),
        ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
        ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)),
        ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)),
        ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)),
        ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)),
        ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb051_alpha_dummy_018 x y A B C))
            (Class.cv (nb051_alpha_dummy_019 x y A B C))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051_alpha_dummy_017 x y A B C))
            (syn_cun (Class.cv (nb051_alpha_dummy_018 x y A B C))
              (Class.cv (nb051_alpha_dummy_019 x y A B C))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb051_alpha_dummy_021 x y z))
            (Class.cv (nb051_alpha_dummy_022 x y z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb051_alpha_dummy_020 x y z))
            (syn_cun (Class.cv (nb051_alpha_dummy_021 x y z))
              (Class.cv (nb051_alpha_dummy_022 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0028 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0029 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0026 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0027 x y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0032 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0033 x y z) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0030 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0031 x y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)),
          ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)),
          ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)),
          ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
          ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)),
          ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)),
          ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)),
          ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)),
          ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
          ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
          ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)),
          ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
          ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
          ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (freshVar_injective
                (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0036 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0037 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0034 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0035 x y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0040 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0041 x y z) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0038 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0039 x y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part021`. -/


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
noncomputable def nb051_split_alpha_0003 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) :
    TAlphaWff
      [((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)),
        ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)),
        ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (Wff.imp (Wff.classMem (Class.cv (nb051_alpha_dummy_037 x y A B C))
          (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))) (Wff.neg
          (Wff.classMem (Class.cv (nb051_alpha_dummy_037 x y A B C))
            (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))
      (Wff.imp (Wff.classMem (Class.cv (nb051_alpha_dummy_038 x y z))
          (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))) (Wff.neg
          (Wff.classMem (Class.cv (nb051_alpha_dummy_038 x y z))
            (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 0))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 1))
                    (TAlphaVar.there (Nat.ne_of_lt
                        (mem_lt_freshVar (nb051_support_mem_0050 x y A B C) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0051 x y z) 0))
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb051_support_mem_0048 x y A B C) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0049 x y z) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb051_alpha_dummy_006 x y z))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb051_support_mem_0024 x y A B C) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb051_support_mem_0025 x y z) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 0)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0022 x y A B C) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb051_alpha_dummy_019 x y A B C),
        (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C),
        (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C),
        (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C),
        (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C),
        (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C),
        (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_037 x y A B C),
        (nb051_alpha_dummy_038 x y z)), ((nb051_alpha_dummy_035 x y A B C),
        (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C),
        (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C),
        (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C),
        (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C),
        (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                                        ((nb051_alpha_dummy_001 x y A B C),
        (nb051_alpha_dummy_002 x y z A B C))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb051_split_alpha_0002 x y z A B C))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
                            ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)),
                            ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)),
                            ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)),
                            ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)),
                            ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
                            ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
                            ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)),
                            ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
                            ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                            ((nb051_alpha_dummy_001 x y A B C),
                              (nb051_alpha_dummy_002 x y z A B C))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
                            ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)),
                            ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)),
                            ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)),
                            ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)),
                            ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
                            ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
                            ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)),
                            ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
                            ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                            ((nb051_alpha_dummy_001 x y A B C),
                              (nb051_alpha_dummy_002 x y z A B C))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt
                        (mem_lt_freshVar (nb051_support_mem_0020 x y A B C) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0021 x y z) 1))
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb051_support_mem_0050 x y A B C) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0051 x y z) 0))
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb051_support_mem_0048 x y A B C) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0049 x y z) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb051_alpha_dummy_006 x y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 1)) (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0024 x y A B C) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0025 x y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb051_support_mem_0023 x y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb051_alpha_dummy_019 x y A B C),
        (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C),
        (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C),
        (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C),
        (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C),
        (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C),
        (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_037 x y A B C),
        (nb051_alpha_dummy_038 x y z)), ((nb051_alpha_dummy_035 x y A B C),
        (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C),
        (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C),
        (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C),
        (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C),
        (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg
                                      (nb051_split_alpha_0002 x y z A B C))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
                              ((nb051_alpha_dummy_011 x y A B C),
                                (nb051_alpha_dummy_013 x y z)),
                              ((nb051_alpha_dummy_012 x y A B C),
                                (nb051_alpha_dummy_014 x y z)),
                              ((nb051_alpha_dummy_037 x y A B C),
                                (nb051_alpha_dummy_038 x y z)),
                              ((nb051_alpha_dummy_035 x y A B C),
                                (nb051_alpha_dummy_036 x y z)),
                              ((nb051_alpha_dummy_004 x y A B C),
                                (nb051_alpha_dummy_006 x y z)),
                              ((nb051_alpha_dummy_003 x y A B C),
                                (nb051_alpha_dummy_005 x y z)),
                              ((nb051_alpha_dummy_033 x y A B C),
                                (nb051_alpha_dummy_034 x y z)),
                              ((nb051_alpha_dummy_007 x y A B C),
                                (nb051_alpha_dummy_008 x y z)),
                              ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                              ((nb051_alpha_dummy_001 x y A B C),
                                (nb051_alpha_dummy_002 x y z A B C))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb051_support_mem_0022 x y A B C) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0023 x y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)),
                              ((nb051_alpha_dummy_011 x y A B C),
                                (nb051_alpha_dummy_013 x y z)),
                              ((nb051_alpha_dummy_012 x y A B C),
                                (nb051_alpha_dummy_014 x y z)),
                              ((nb051_alpha_dummy_037 x y A B C),
                                (nb051_alpha_dummy_038 x y z)),
                              ((nb051_alpha_dummy_035 x y A B C),
                                (nb051_alpha_dummy_036 x y z)),
                              ((nb051_alpha_dummy_004 x y A B C),
                                (nb051_alpha_dummy_006 x y z)),
                              ((nb051_alpha_dummy_003 x y A B C),
                                (nb051_alpha_dummy_005 x y z)),
                              ((nb051_alpha_dummy_033 x y A B C),
                                (nb051_alpha_dummy_034 x y z)),
                              ((nb051_alpha_dummy_007 x y A B C),
                                (nb051_alpha_dummy_008 x y z)),
                              ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                              ((nb051_alpha_dummy_001 x y A B C),
                                (nb051_alpha_dummy_002 x y z A B C))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part024`. -/


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
noncomputable def nb051_variable_occurrence (x y z : Var) (A B C : Class) :
    TAlphaClass
      [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)),
        ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)),
        ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)),
        ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)),
        ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Class.cv z) :=
  by
  have freshness0 :
    (nb051_alpha_dummy_000 x y A B C) ≠ (nb051_alpha_dummy_004 x y A B C) :=
    by
    unfold nb051_alpha_dummy_004
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 1))
  have freshness1 : z ≠ (nb051_alpha_dummy_006 x y z) :=
    by
    unfold nb051_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 1))
  have freshness2 :
    (nb051_alpha_dummy_000 x y A B C) ≠ (nb051_alpha_dummy_003 x y A B C) :=
    by
    unfold nb051_alpha_dummy_003
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0042 x y A B C) 0))
  have freshness3 : z ≠ (nb051_alpha_dummy_005 x y z) :=
    by
    unfold nb051_alpha_dummy_005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0044 x y z) 0))
  have freshness4 :
    (nb051_alpha_dummy_000 x y A B C) ≠ (nb051_alpha_dummy_033 x y A B C) :=
    by
    unfold nb051_alpha_dummy_033
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0046 x y A B C) 0))
  have freshness5 : z ≠ (nb051_alpha_dummy_034 x y z) :=
    by
    unfold nb051_alpha_dummy_034
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0047 x y z) 0))
  have freshness6 :
    (nb051_alpha_dummy_000 x y A B C) ≠ (nb051_alpha_dummy_007 x y A B C) :=
    by
    unfold nb051_alpha_dummy_007
    with_reducible
      exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0043 x y A B C) 0))
  have freshness7 : z ≠ (nb051_alpha_dummy_008 x y z) :=
    by
    unfold nb051_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0045 x y z) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

@[expose]
noncomputable def nb051_split_alpha_0004 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (Wff.classEq (Class.cv (nb051_alpha_dummy_001 x y A B C))
        (syn_cop (syn_cop (Class.cv x) (Class.cv y))
          (Class.cv (nb051_alpha_dummy_000 x y A B C))))
      (Wff.classEq (Class.cv (nb051_alpha_dummy_002 x y z A B C))
        (syn_cop (syn_cop (Class.cv x) (Class.cv y)) (Class.cv z))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0004 x y A B C) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0005 x y z A B C) 0)))
        (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0)))
          (TAlphaVar.there (Ne.symm
              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0))) (Ne.symm
              (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0)))
            (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg
                          (nb051_split_alpha_0001 x y z A B C dv_x_z dv_y_z)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg
                          (nb051_split_alpha_0001 x y z A B C dv_x_z dv_y_z)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (nb051_variable_occurrence x y z A B C)) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                    ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv)
                                  (by decide)) (freshVar_injective
                                  (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb051_split_alpha_0003 x y z A B C))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb051_alpha_dummy_035 x y A B C),
        (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C),
        (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C),
        (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C),
        (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C),
        (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                                        ((nb051_alpha_dummy_001 x y A B C),
        (nb051_alpha_dummy_002 x y z A B C))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (nb051_variable_occurrence x y z A B C)) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
                                    ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv)
                                  (by decide)) (freshVar_injective
                                  (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb051_split_alpha_0003 x y z A B C))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb051_alpha_dummy_035 x y A B C),
        (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C),
        (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C),
        (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C),
        (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C),
        (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                                        ((nb051_alpha_dummy_001 x y A B C),
        (nb051_alpha_dummy_002 x y z A B C))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part025`. -/


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

theorem nb051_focused_notmem_0000 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ A.fv :=
  by
  change
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))))

theorem nb051_focused_notmem_0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ B.fv :=
  by
  change
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb051_wpp_notmem_0110 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∉
      ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  simpa only [nb051_alpha_dummy_000, fv_syn_wa, Finset.mem_union, fv_wff_classMem,
    fv_class_cv, Finset.mem_singleton, not_or] using
    (And.intro (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0018 x y A B C) 0)))
        (nb051_focused_notmem_0000 x y A B C)) (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0019 x y A B C) 0)))
        (nb051_focused_notmem_0001 x y A B C)))

theorem nb051_wpp_notmem_0111 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    z ∉ ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  simp only [fv_syn_wa, Finset.mem_union, fv_wff_classMem, fv_class_cv, (Ne.symm dv_x_z),
    Finset.mem_singleton, dv_A_z, (Ne.symm dv_y_z), dv_B_z, or_false, not_false_eq_true]

theorem nb051_focused_notmem_0002 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
          ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C)).symm ▸
            (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                    (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_left _
                  (((fv_wff_classMem (Class.cv x) A).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_focused_notmem_0003 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
          ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C)).symm ▸
            (Finset.mem_union_left _ (((fv_syn_wa (Wff.classMem (Class.cv x) A)
                    (Wff.classMem (Class.cv y) B)).symm ▸ (Finset.mem_union_right _
                  (((fv_wff_classMem (Class.cv y) B).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_wpp_notmem_0112 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_001 x y A B C) ∉
      ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  simpa only [nb051_alpha_dummy_001, fv_syn_wa, Finset.mem_union, fv_wff_classMem,
    fv_class_cv, Finset.mem_singleton, not_or] using
    (And.intro (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0000 x y A B C) 0)))
        (nb051_focused_notmem_0002 x y A B C)) (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0002 x y A B C) 0)))
        (nb051_focused_notmem_0003 x y A B C)))

theorem nb051_focused_notmem_0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ A.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv z) C))).fv)
        0 ∉
      A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_left _
              (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸
                (Finset.mem_union_left _ (((fv_wff_classMem (Class.cv x) A).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_focused_notmem_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ B.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv z) C))).fv)
        0 ∉
      B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_left _
              (((fv_syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)).symm ▸
                (Finset.mem_union_right _ (((fv_wff_classMem (Class.cv y) B).symm ▸
                    (Finset.mem_union_right _ (hu)))))))))))

theorem nb051_wpp_notmem_0113 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) :
    (nb051_alpha_dummy_002 x y z A B C) ∉
      ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  simpa only [nb051_alpha_dummy_002, fv_syn_wa, Finset.mem_union, fv_wff_classMem,
    fv_class_cv, Finset.mem_singleton, not_or] using
    (And.intro (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0001 x y z A B C) 0)))
        (nb051_focused_notmem_0004 x y z A B C)) (And.intro
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb051_support_mem_0003 x y z A B C) 0)))
        (nb051_focused_notmem_0005 x y z A B C)))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part026`. -/


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

theorem nb051_compact_envfresh_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    TEnvFresh
      [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0110 x y A B C)
      (nb051_wpp_notmem_0111 x y z A B dv_A_z dv_B_z dv_x_z dv_y_z) (TEnvFresh.consSame y
        (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C)
            (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0112 x y A B C)
            (nb051_wpp_notmem_0113 x y z A B C) (TEnvFresh.nil
              ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv)))))

@[expose]
noncomputable def nb051_wpp_refl_0008 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    TReflOn
      [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0008 x y z A B C dv_A_z dv_B_z dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part027`. -/


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

theorem nb051_focused_notmem_0006 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ C.fv :=
  by
  change
    freshVar (({ x } : Finset Var) ∪ (A).fv ∪ ({ y } : Finset Var) ∪ (B).fv ∪ (C).fv) 0 ∉
      C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb051_wpp_notmem_0114 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_000 x y A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0006 x y A B C), not_false_eq_true]

theorem nb051_wpp_notmem_0115 (z : Var) (C : Class) (dv_C_z : z ∉ C.fv) : z ∉ (C).fv := by
  simp only [dv_C_z, not_false_eq_true]

theorem nb051_focused_notmem_0007 (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ C.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
            ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪
          ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv)
        0 ∉
      C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C)).symm ▸
            (Finset.mem_union_right _
              (((fv_wff_classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C).symm ▸
                (Finset.mem_union_right _ (hu))))))))

theorem nb051_wpp_notmem_0116 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) :
    (nb051_alpha_dummy_001 x y A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0007 x y A B C), not_false_eq_true]

theorem nb051_focused_notmem_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ C.fv :=
  by
  change
    freshVar
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
              (Wff.classEq (Class.cv z) C))).fv)
        0 ∉
      C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (((fv_syn_wa
                (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                (Wff.classEq (Class.cv z) C)).symm ▸ (Finset.mem_union_right _
              (((fv_wff_classEq (Class.cv z) C).symm ▸ (Finset.mem_union_right _ (hu))))))))

theorem nb051_wpp_notmem_0117 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ (C).fv := by
  simp only [(nb051_focused_notmem_0008 x y z A B C), not_false_eq_true]

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part028`. -/


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

theorem nb051_compact_envfresh_0009 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_C_z : z ∉ C.fv) :
    TEnvFresh
      [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (C).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z
      (nb051_wpp_notmem_0114 x y A B C) (nb051_wpp_notmem_0115 z C dv_C_z) (TEnvFresh.consSame y
        (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C)
            (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0116 x y A B C)
            (nb051_wpp_notmem_0117 x y z A B C) (TEnvFresh.nil (C).fv)))))

@[expose]
noncomputable def nb051_wpp_refl_0009 (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (dv_C_z : z ∉ C.fv) :
    TReflOn
      [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
        ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
      (C).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0009 x y z A B C dv_C_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAPD051C001Part029`. -/


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
noncomputable def nominal_df_mpt2 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_C_z : z ∉ C.fv)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cmpt2 x A y B C) (syn_coprab x y z
          (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
            (.classEq (.cv z) C)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex
              (TAlphaWff.conj (nb051_split_alpha_0004 x y z A B C dv_x_z dv_y_z) (TAlphaWff.conj
                  (TAlphaWff.refl_of_reflOn
                    [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                      ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))]
                    (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))
                    (nb051_wpp_refl_0008 x y z A B C dv_A_z dv_B_z dv_x_z dv_y_z))
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.refl_of_reflOn
                      [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x),
                        ((nb051_alpha_dummy_001 x y A B C),
                          (nb051_alpha_dummy_002 x y z A B C))]
                      C (nb051_wpp_refl_0009 x y z A B C dv_C_z)))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
