/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C053C001Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C053C001Part002`. -/


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
noncomputable def nb053_split_alpha_0000 (x : Var) (y : Var) :
    TAlphaWff
      [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)),
        ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
        ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)),
        ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
        ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
        ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
        ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
        ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)),
        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
        ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
        ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_018))
            (syn_cun (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb053_alpha_dummy_021 x y))
            (syn_cun (Class.cv (nb053_alpha_dummy_022 x y))
              (Class.cv (nb053_alpha_dummy_023 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)),
          ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
          ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)),
          ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
          ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
          ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
          ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
          ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
          ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)),
          ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
          ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
          ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb053_split_alpha_0001 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
        ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)),
        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
        ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
        ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb053_alpha_dummy_005))
          (Class.cv (nb053_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (Class.cv (nb053_alpha_dummy_004))
            (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))
      (Wff.imp (Wff.classMem (Class.cv (nb053_alpha_dummy_007 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb053_alpha_dummy_006 x y))
            (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0009 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0007 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb053_alpha_dummy_000))).fv ∪
                ((Class.cv (nb053_alpha_dummy_001))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_005))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb053_alpha_dummy_007 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb053_alpha_dummy_020),
        (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
        ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016),
        (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
        ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_005),
        (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
        ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)), ((nb053_alpha_dummy_008),
        (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y),
        ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb053_split_alpha_0000 x y))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                              ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                              ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                              ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                              ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                              ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)),
                              ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                              ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                              ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                              ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                              ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                              ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                              ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                              ((nb053_alpha_dummy_010), (nb053_alpha_dummy_011 x y)),
                              ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                              ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                              ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb053_split_alpha_0002 (x : Var) (y : Var) :
    TAlphaWff
      [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)),
        ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
        ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)),
        ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
        ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
        ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
        ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
        ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
        ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
        ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
        ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
        ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb053_alpha_dummy_018))
            (syn_cun (Class.cv (nb053_alpha_dummy_019)) (Class.cv (nb053_alpha_dummy_020))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb053_alpha_dummy_022 x y))
            (Class.cv (nb053_alpha_dummy_023 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb053_alpha_dummy_021 x y))
            (syn_cun (Class.cv (nb053_alpha_dummy_022 x y))
              (Class.cv (nb053_alpha_dummy_023 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb053_alpha_dummy_020), (nb053_alpha_dummy_023 x y)),
          ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
          ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)),
          ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
          ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
          ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
          ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
          ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
          ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
          ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
          ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
          ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
          ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
          ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C053C001Part003`. -/


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
noncomputable def nb053_split_alpha_0003 (x : Var) (y : Var) :
    TAlphaWff
      [((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
        ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
        ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
        ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
        ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
        ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
      (Wff.imp (Wff.classMem (Class.cv (nb053_alpha_dummy_038))
          (syn_cphi (Class.cv (nb053_alpha_dummy_005)))) (Wff.neg
          (Wff.classMem (Class.cv (nb053_alpha_dummy_038))
            (syn_cphi (Class.cv (nb053_alpha_dummy_005))))))
      (Wff.imp (Wff.classMem (Class.cv (nb053_alpha_dummy_039 x y))
          (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))) (Wff.neg
          (Wff.classMem (Class.cv (nb053_alpha_dummy_039 x y))
            (syn_cphi (Class.cv (nb053_alpha_dummy_007 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0041 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0039 x y) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_005))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb053_alpha_dummy_007 x y))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0015 x y) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0015 x y) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb053_alpha_dummy_020),
        (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
                                        ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)),
                                        ((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                                        ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                                        ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                                        ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
                                        ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
                                        ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                                        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                                        ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                                        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                                        ((nb053_alpha_dummy_001), y),
                                        ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002),
        (nb053_alpha_dummy_003 x y))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb053_split_alpha_0002 x y))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                            ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                            ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                            ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
                            ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
                            ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                            ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                            ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                            ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                            ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                            ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                            ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                            ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                            ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
                            ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
                            ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                            ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                            ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                            ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                            ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                            ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0011 x y) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0041 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0039 x y) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb053_alpha_dummy_005))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb053_alpha_dummy_007 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0015 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0015 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb053_support_mem_0013 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb053_alpha_dummy_020),
        (nb053_alpha_dummy_023 x y)), ((nb053_alpha_dummy_019), (nb053_alpha_dummy_022 x y)),
        ((nb053_alpha_dummy_018), (nb053_alpha_dummy_021 x y)), ((nb053_alpha_dummy_016),
        (nb053_alpha_dummy_017 x y)), ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
        ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)), ((nb053_alpha_dummy_038),
        (nb053_alpha_dummy_039 x y)), ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
        ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)), ((nb053_alpha_dummy_004),
        (nb053_alpha_dummy_006 x y)), ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)), ((nb053_alpha_dummy_001), y),
        ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb053_split_alpha_0002 x y))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                              ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                              ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                              ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
                              ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
                              ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                              ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                              ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                              ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                              ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                              ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0013 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb053_alpha_dummy_016), (nb053_alpha_dummy_017 x y)),
                              ((nb053_alpha_dummy_012), (nb053_alpha_dummy_014 x y)),
                              ((nb053_alpha_dummy_013), (nb053_alpha_dummy_015 x y)),
                              ((nb053_alpha_dummy_038), (nb053_alpha_dummy_039 x y)),
                              ((nb053_alpha_dummy_036), (nb053_alpha_dummy_037 x y)),
                              ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                              ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                              ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                              ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                              ((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                              ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb053_split_alpha_0004 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
        ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
      (Wff.classEq (Class.cv (nb053_alpha_dummy_002))
        (syn_cop (Class.cv (nb053_alpha_dummy_000)) (Class.cv (nb053_alpha_dummy_001))))
      (Wff.classEq (Class.cv (nb053_alpha_dummy_003 x y))
        (syn_cop (Class.cv x) (Class.cv y))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0002) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0003 x y) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0000) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb053_support_mem_0001 x y) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb053_split_alpha_0001 x y dv_x_y)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb053_split_alpha_0001 x y dv_x_y)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb053_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb053_support_mem_0034 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb053_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb053_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb053_split_alpha_0003 x y)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb053_alpha_dummy_036),
        (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                                        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                                        ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                                        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                                        ((nb053_alpha_dummy_001), y),
                                        ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002),
        (nb053_alpha_dummy_003 x y))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb053_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb053_support_mem_0034 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb053_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0037 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0035 x y) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb053_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb053_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb053_split_alpha_0003 x y)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb053_alpha_dummy_036),
        (nb053_alpha_dummy_037 x y)), ((nb053_alpha_dummy_005), (nb053_alpha_dummy_007 x y)),
                                        ((nb053_alpha_dummy_004), (nb053_alpha_dummy_006 x y)),
                                        ((nb053_alpha_dummy_034), (nb053_alpha_dummy_035 x y)),
                                        ((nb053_alpha_dummy_008), (nb053_alpha_dummy_009 x y)),
                                        ((nb053_alpha_dummy_001), y),
                                        ((nb053_alpha_dummy_000), x), ((nb053_alpha_dummy_002),
        (nb053_alpha_dummy_003 x y))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nominal_df_disj (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cdisj) (syn_copab x y (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb053_split_alpha_0004 x y dv_x_y) (TAlphaWff.classEq
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0004) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0042) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0043 x y) 0))
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0032) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0044) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0045 x y) 0))
                                      (TAlphaVar.here _ _ _)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0004) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0006 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0042) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0043 x y) 0))
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0032) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb053_support_mem_0034 x y) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0044) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb053_support_mem_0045 x y) 0))
                                      (TAlphaVar.here _ _ _))))))))))))
                (TAlphaClass.refl_of_closed
                  [((nb053_alpha_dummy_001), y), ((nb053_alpha_dummy_000), x),
                    ((nb053_alpha_dummy_002), (nb053_alpha_dummy_003 x y))]
                  (syn_c0) (by simp only [fv_syn_c0])))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
