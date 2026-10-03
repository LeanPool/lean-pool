/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C063C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C063C001Part004`. -/


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
noncomputable def nb063_split_alpha_0000 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_022), (nb063_alpha_dummy_025 r a)),
        ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
        ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)),
        ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
        ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
        ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
        ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
        ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)),
        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb063_alpha_dummy_020))
            (syn_cun (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb063_alpha_dummy_024 r a))
            (Class.cv (nb063_alpha_dummy_025 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_023 r a))
            (syn_cun (Class.cv (nb063_alpha_dummy_024 r a))
              (Class.cv (nb063_alpha_dummy_025 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb063_alpha_dummy_022), (nb063_alpha_dummy_025 r a)),
          ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
          ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)),
          ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
          ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
          ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
          ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
          ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
          ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)),
          ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
          ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
          ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0001 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
        ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)),
        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_007))
          (Class.cv (nb063_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_006))
            (syn_cphi (Class.cv (nb063_alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_009 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_008 r a))
            (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_001))).fv ∪
                ((Class.cv (nb063_alpha_dummy_000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb063_alpha_dummy_007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb063_alpha_dummy_009 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_022),
        (nb063_alpha_dummy_025 r a)), ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
        ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)), ((nb063_alpha_dummy_018),
        (nb063_alpha_dummy_019 r a)), ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
        ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)), ((nb063_alpha_dummy_007),
        (nb063_alpha_dummy_009 r a)), ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
        ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)), ((nb063_alpha_dummy_010),
        (nb063_alpha_dummy_011 r a)), ((nb063_alpha_dummy_000), a),
        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb063_split_alpha_0000 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                              ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                              ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                              ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                              ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                              ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)),
                              ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                              ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                              ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                              ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                              ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                              ((nb063_alpha_dummy_012), (nb063_alpha_dummy_013 r a)),
                              ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0002 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_022), (nb063_alpha_dummy_025 r a)),
        ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
        ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)),
        ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
        ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
        ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
        ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
        ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
        ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
        ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb063_alpha_dummy_020))
            (syn_cun (Class.cv (nb063_alpha_dummy_021)) (Class.cv (nb063_alpha_dummy_022))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb063_alpha_dummy_024 r a))
            (Class.cv (nb063_alpha_dummy_025 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_023 r a))
            (syn_cun (Class.cv (nb063_alpha_dummy_024 r a))
              (Class.cv (nb063_alpha_dummy_025 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb063_alpha_dummy_022), (nb063_alpha_dummy_025 r a)),
          ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
          ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)),
          ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
          ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
          ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
          ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
          ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
          ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
          ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
          ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
          ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
          ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
          ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_014))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_016 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0003 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
        ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
        ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
        ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_040))
          (syn_cphi (Class.cv (nb063_alpha_dummy_007)))) (Wff.neg
          (Wff.classMem (Class.cv (nb063_alpha_dummy_040))
            (syn_cphi (Class.cv (nb063_alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_041 r a))
          (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb063_alpha_dummy_041 r a))
            (syn_cphi (Class.cv (nb063_alpha_dummy_009 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb063_alpha_dummy_007))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb063_alpha_dummy_009 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_022),
        (nb063_alpha_dummy_025 r a)), ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
                                        ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)),
                                        ((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                                        ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                                        ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                                        ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
                                        ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
                                        ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                                        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                                        ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                                        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                                        ((nb063_alpha_dummy_000), a),
                                        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb063_split_alpha_0002 x y r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                            ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                            ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                            ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
                            ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
                            ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                            ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                            ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                            ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                            ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                            ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                            ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                            ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                            ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
                            ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
                            ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                            ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                            ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                            ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                            ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                            ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb063_alpha_dummy_007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb063_alpha_dummy_009 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_022),
        (nb063_alpha_dummy_025 r a)), ((nb063_alpha_dummy_021), (nb063_alpha_dummy_024 r a)),
        ((nb063_alpha_dummy_020), (nb063_alpha_dummy_023 r a)), ((nb063_alpha_dummy_018),
        (nb063_alpha_dummy_019 r a)), ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
        ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)), ((nb063_alpha_dummy_040),
        (nb063_alpha_dummy_041 r a)), ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
        ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)), ((nb063_alpha_dummy_006),
        (nb063_alpha_dummy_008 r a)), ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)), ((nb063_alpha_dummy_000), a),
        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb063_split_alpha_0002 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                              ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                              ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                              ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
                              ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
                              ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                              ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                              ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                              ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_018), (nb063_alpha_dummy_019 r a)),
                              ((nb063_alpha_dummy_014), (nb063_alpha_dummy_016 r a)),
                              ((nb063_alpha_dummy_015), (nb063_alpha_dummy_017 r a)),
                              ((nb063_alpha_dummy_040), (nb063_alpha_dummy_041 r a)),
                              ((nb063_alpha_dummy_038), (nb063_alpha_dummy_039 r a)),
                              ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                              ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                              ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                              ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C063C001Part005`. -/


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
noncomputable def nb063_pair_occurrence (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaClass
      [((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Class.cv (nb063_alpha_dummy_004)) (Class.cv (nb063_alpha_dummy_005 x y r a)) :=
  by
  have freshness0 : (nb063_alpha_dummy_004) ≠ (nb063_alpha_dummy_000) :=
    by
    unfold nb063_alpha_dummy_004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0002) 0)))
  have freshness1 : (nb063_alpha_dummy_005 x y r a) ≠ a :=
    by
    unfold nb063_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0003 x y r a) 0)))
  have freshness2 : (nb063_alpha_dummy_004) ≠ (nb063_alpha_dummy_001) :=
    by
    unfold nb063_alpha_dummy_004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0000) 0)))
  have freshness3 : (nb063_alpha_dummy_005 x y r a) ≠ r :=
    by
    unfold nb063_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0001 x y r a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb063_split_alpha_0004 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.classEq (Class.cv (nb063_alpha_dummy_004))
        (syn_cop (Class.cv (nb063_alpha_dummy_001)) (Class.cv (nb063_alpha_dummy_000))))
      (Wff.classEq (Class.cv (nb063_alpha_dummy_005 x y r a))
        (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (nb063_pair_occurrence x y r a) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb063_split_alpha_0001 x y r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb063_split_alpha_0001 x y r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb063_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb063_split_alpha_0003 x y r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_038),
        (nb063_alpha_dummy_039 r a)), ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                                        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                                        ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                                        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                                        ((nb063_alpha_dummy_000), a),
                                        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb063_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb063_split_alpha_0003 x y r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_038),
        (nb063_alpha_dummy_039 r a)), ((nb063_alpha_dummy_007), (nb063_alpha_dummy_009 r a)),
                                        ((nb063_alpha_dummy_006), (nb063_alpha_dummy_008 r a)),
                                        ((nb063_alpha_dummy_036), (nb063_alpha_dummy_037 r a)),
                                        ((nb063_alpha_dummy_010), (nb063_alpha_dummy_011 r a)),
                                        ((nb063_alpha_dummy_000), a),
                                        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0005 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_058), (nb063_alpha_dummy_061 x y)),
        ((nb063_alpha_dummy_057), (nb063_alpha_dummy_060 x y)),
        ((nb063_alpha_dummy_056), (nb063_alpha_dummy_059 x y)),
        ((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
        ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
        ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
        ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
        ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
        ((nb063_alpha_dummy_048), (nb063_alpha_dummy_049 x y)),
        ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb063_alpha_dummy_056))
            (syn_cun (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb063_alpha_dummy_060 x y))
            (Class.cv (nb063_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_059 x y))
            (syn_cun (Class.cv (nb063_alpha_dummy_060 x y))
              (Class.cv (nb063_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb063_alpha_dummy_058), (nb063_alpha_dummy_061 x y)),
          ((nb063_alpha_dummy_057), (nb063_alpha_dummy_060 x y)),
          ((nb063_alpha_dummy_056), (nb063_alpha_dummy_059 x y)),
          ((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
          ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
          ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
          ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
          ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
          ((nb063_alpha_dummy_048), (nb063_alpha_dummy_049 x y)),
          ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
          ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
          ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
          ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0006 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
        ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
        ((nb063_alpha_dummy_048), (nb063_alpha_dummy_049 x y)),
        ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_043))
          (Class.cv (nb063_alpha_dummy_002))) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_042))
            (syn_cphi (Class.cv (nb063_alpha_dummy_043))))))
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_045 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y))
            (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0044 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0047 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0045 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_002))).fv ∪
                ((Class.cv (nb063_alpha_dummy_003))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0049 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0049 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb063_alpha_dummy_043))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb063_alpha_dummy_045 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0053 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_058),
        (nb063_alpha_dummy_061 x y)), ((nb063_alpha_dummy_057), (nb063_alpha_dummy_060 x y)),
        ((nb063_alpha_dummy_056), (nb063_alpha_dummy_059 x y)), ((nb063_alpha_dummy_054),
        (nb063_alpha_dummy_055 x y)), ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
        ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)), ((nb063_alpha_dummy_043),
        (nb063_alpha_dummy_045 x y)), ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
        ((nb063_alpha_dummy_048), (nb063_alpha_dummy_049 x y)), ((nb063_alpha_dummy_046),
        (nb063_alpha_dummy_047 x y)), ((nb063_alpha_dummy_003), y),
        ((nb063_alpha_dummy_002), x), ((nb063_alpha_dummy_000), a),
        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb063_split_alpha_0005 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
                              ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
                              ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
                              ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                              ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                              ((nb063_alpha_dummy_048), (nb063_alpha_dummy_049 x y)),
                              ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                              ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
                              ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
                              ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
                              ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                              ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                              ((nb063_alpha_dummy_048), (nb063_alpha_dummy_049 x y)),
                              ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                              ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C063C001Part006`. -/


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
noncomputable def nb063_split_alpha_0007 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_058), (nb063_alpha_dummy_061 x y)),
        ((nb063_alpha_dummy_057), (nb063_alpha_dummy_060 x y)),
        ((nb063_alpha_dummy_056), (nb063_alpha_dummy_059 x y)),
        ((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
        ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
        ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
        ((nb063_alpha_dummy_076), (nb063_alpha_dummy_077 x y)),
        ((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
        ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
        ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
        ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
        ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb063_alpha_dummy_056))
            (syn_cun (Class.cv (nb063_alpha_dummy_057)) (Class.cv (nb063_alpha_dummy_058))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb063_alpha_dummy_060 x y))
            (Class.cv (nb063_alpha_dummy_061 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_059 x y))
            (syn_cun (Class.cv (nb063_alpha_dummy_060 x y))
              (Class.cv (nb063_alpha_dummy_061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb063_alpha_dummy_058), (nb063_alpha_dummy_061 x y)),
          ((nb063_alpha_dummy_057), (nb063_alpha_dummy_060 x y)),
          ((nb063_alpha_dummy_056), (nb063_alpha_dummy_059 x y)),
          ((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
          ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
          ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
          ((nb063_alpha_dummy_076), (nb063_alpha_dummy_077 x y)),
          ((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
          ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
          ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
          ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
          ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
          ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
          ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
          ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0008 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
        ((nb063_alpha_dummy_076), (nb063_alpha_dummy_077 x y)),
        ((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
        ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
        ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
        ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
        ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.all (nb063_alpha_dummy_050) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (nb063_alpha_dummy_050)) (Class.cv (nb063_alpha_dummy_043)))
            (Wff.classEq (Class.cv (nb063_alpha_dummy_051))
              (syn_cif (Wff.classMem (Class.cv (nb063_alpha_dummy_050)) (syn_cnnc))
                (syn_cplc (Class.cv (nb063_alpha_dummy_050)) (syn_c1c))
                (Class.cv (nb063_alpha_dummy_050)))))))
      (Wff.all (nb063_alpha_dummy_052 x y) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (nb063_alpha_dummy_052 x y))
              (Class.cv (nb063_alpha_dummy_045 x y)))
            (Wff.classEq (Class.cv (nb063_alpha_dummy_053 x y))
              (syn_cif (Wff.classMem (Class.cv (nb063_alpha_dummy_052 x y)) (syn_cnnc))
                (syn_cplc (Class.cv (nb063_alpha_dummy_052 x y)) (syn_c1c))
                (Class.cv (nb063_alpha_dummy_052 x y))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0048) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0049 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0048) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0049 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0078) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0079 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0076) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0077 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_043))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_045 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0052) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0053 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0052) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0053 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0050) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb063_alpha_dummy_058), (nb063_alpha_dummy_061 x y)),
                                    ((nb063_alpha_dummy_057), (nb063_alpha_dummy_060 x y)),
                                    ((nb063_alpha_dummy_056), (nb063_alpha_dummy_059 x y)),
                                    ((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
                                    ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
                                    ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
                                    ((nb063_alpha_dummy_076), (nb063_alpha_dummy_077 x y)),
                                    ((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
                                    ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                                    ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                                    ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
                                    ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                                    ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                                    ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                                    ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb063_split_alpha_0007 x y r a))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
                        ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
                        ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
                        ((nb063_alpha_dummy_076), (nb063_alpha_dummy_077 x y)),
                        ((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
                        ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                        ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                        ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
                        ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0051 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb063_alpha_dummy_054), (nb063_alpha_dummy_055 x y)),
                        ((nb063_alpha_dummy_050), (nb063_alpha_dummy_052 x y)),
                        ((nb063_alpha_dummy_051), (nb063_alpha_dummy_053 x y)),
                        ((nb063_alpha_dummy_076), (nb063_alpha_dummy_077 x y)),
                        ((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
                        ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                        ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                        ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
                        ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def nb063_split_alpha_0009 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_046)) (syn_ccompl
            (Class.cab (nb063_alpha_dummy_042)
              (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb063_alpha_dummy_042))
                  (syn_cphi (Class.cv (nb063_alpha_dummy_043)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb063_alpha_dummy_046)) (syn_ccompl
              (Class.cab (nb063_alpha_dummy_042)
                (syn_wrex (nb063_alpha_dummy_043) (Class.cv (nb063_alpha_dummy_003))
                  (Wff.classEq (Class.cv (nb063_alpha_dummy_042))
                    (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_043)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_047 x y)) (syn_ccompl
            (Class.cab (nb063_alpha_dummy_044 x y)
              (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb063_alpha_dummy_047 x y)) (syn_ccompl
              (Class.cab (nb063_alpha_dummy_044 x y)
                (syn_wrex (nb063_alpha_dummy_045 x y) (Class.cv y)
                  (Wff.classEq (Class.cv (nb063_alpha_dummy_044 x y))
                    (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_045 x y)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb063_split_alpha_0006 x y r a dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb063_split_alpha_0006 x y r a dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 0))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0074) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0075 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0071) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0073 x y) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb063_alpha_dummy_002))).fv ∪
                                ((Class.cv (nb063_alpha_dummy_003))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb063_split_alpha_0008 x y r a)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb063_split_alpha_0008 x y r a))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
                                    ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                                    ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                                    ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
                                    ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                                    ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                                    ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                                    ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0072 x y) 0))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0074) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0075 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0071) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0073 x y) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb063_alpha_dummy_002))).fv ∪
                                ((Class.cv (nb063_alpha_dummy_003))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb063_split_alpha_0008 x y r a)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb063_split_alpha_0008 x y r a))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb063_alpha_dummy_074), (nb063_alpha_dummy_075 x y)),
                                    ((nb063_alpha_dummy_043), (nb063_alpha_dummy_045 x y)),
                                    ((nb063_alpha_dummy_042), (nb063_alpha_dummy_044 x y)),
                                    ((nb063_alpha_dummy_072), (nb063_alpha_dummy_073 x y)),
                                    ((nb063_alpha_dummy_046), (nb063_alpha_dummy_047 x y)),
                                    ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                                    ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                                    ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                                  (syn_ccompl (syn_csn (syn_c0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0010 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_094), (nb063_alpha_dummy_097 x y)),
        ((nb063_alpha_dummy_093), (nb063_alpha_dummy_096 x y)),
        ((nb063_alpha_dummy_092), (nb063_alpha_dummy_095 x y)),
        ((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
        ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
        ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
        ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
        ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
        ((nb063_alpha_dummy_084), (nb063_alpha_dummy_085 x y)),
        ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb063_alpha_dummy_092))
            (syn_cun (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb063_alpha_dummy_096 x y))
            (Class.cv (nb063_alpha_dummy_097 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_095 x y))
            (syn_cun (Class.cv (nb063_alpha_dummy_096 x y))
              (Class.cv (nb063_alpha_dummy_097 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb063_alpha_dummy_094), (nb063_alpha_dummy_097 x y)),
          ((nb063_alpha_dummy_093), (nb063_alpha_dummy_096 x y)),
          ((nb063_alpha_dummy_092), (nb063_alpha_dummy_095 x y)),
          ((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
          ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
          ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
          ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
          ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
          ((nb063_alpha_dummy_084), (nb063_alpha_dummy_085 x y)),
          ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
          ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
          ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
          ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C063C001Part007`. -/


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
noncomputable def nb063_split_alpha_0011 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
        ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
        ((nb063_alpha_dummy_084), (nb063_alpha_dummy_085 x y)),
        ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_079))
          (Class.cv (nb063_alpha_dummy_003))) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_078))
            (syn_cphi (Class.cv (nb063_alpha_dummy_079))))))
      (Wff.imp (Wff.classMem (Class.cv (nb063_alpha_dummy_081 x y)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y))
            (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0080) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0082 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0084) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0085 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0081) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0083 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb063_alpha_dummy_003))).fv ∪
                ((Class.cv (nb063_alpha_dummy_002))).fv) (by decide))
            (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0086) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0087 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0086) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0087 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb063_alpha_dummy_079))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb063_alpha_dummy_081 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0090) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb063_support_mem_0091 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0090) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0091 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0088) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb063_support_mem_0089 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb063_alpha_dummy_094),
        (nb063_alpha_dummy_097 x y)), ((nb063_alpha_dummy_093), (nb063_alpha_dummy_096 x y)),
        ((nb063_alpha_dummy_092), (nb063_alpha_dummy_095 x y)), ((nb063_alpha_dummy_090),
        (nb063_alpha_dummy_091 x y)), ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
        ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)), ((nb063_alpha_dummy_079),
        (nb063_alpha_dummy_081 x y)), ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
        ((nb063_alpha_dummy_084), (nb063_alpha_dummy_085 x y)), ((nb063_alpha_dummy_082),
        (nb063_alpha_dummy_083 x y)), ((nb063_alpha_dummy_003), y),
        ((nb063_alpha_dummy_002), x), ((nb063_alpha_dummy_000), a),
        ((nb063_alpha_dummy_001), r), ((nb063_alpha_dummy_004),
        (nb063_alpha_dummy_005 x y r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb063_split_alpha_0010 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
                              ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
                              ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
                              ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                              ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                              ((nb063_alpha_dummy_084), (nb063_alpha_dummy_085 x y)),
                              ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                              ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0088) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
                              ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
                              ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
                              ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                              ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                              ((nb063_alpha_dummy_084), (nb063_alpha_dummy_085 x y)),
                              ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                              ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                              ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                              ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0012 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_094), (nb063_alpha_dummy_097 x y)),
        ((nb063_alpha_dummy_093), (nb063_alpha_dummy_096 x y)),
        ((nb063_alpha_dummy_092), (nb063_alpha_dummy_095 x y)),
        ((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
        ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
        ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
        ((nb063_alpha_dummy_112), (nb063_alpha_dummy_113 x y)),
        ((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
        ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
        ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
        ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
        ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb063_alpha_dummy_092))
            (syn_cun (Class.cv (nb063_alpha_dummy_093)) (Class.cv (nb063_alpha_dummy_094))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb063_alpha_dummy_096 x y))
            (Class.cv (nb063_alpha_dummy_097 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb063_alpha_dummy_095 x y))
            (syn_cun (Class.cv (nb063_alpha_dummy_096 x y))
              (Class.cv (nb063_alpha_dummy_097 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb063_alpha_dummy_094), (nb063_alpha_dummy_097 x y)),
          ((nb063_alpha_dummy_093), (nb063_alpha_dummy_096 x y)),
          ((nb063_alpha_dummy_092), (nb063_alpha_dummy_095 x y)),
          ((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
          ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
          ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
          ((nb063_alpha_dummy_112), (nb063_alpha_dummy_113 x y)),
          ((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
          ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
          ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
          ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
          ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
          ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
          ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
          ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_086))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb063_alpha_dummy_088 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb063_split_alpha_0013 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
        ((nb063_alpha_dummy_112), (nb063_alpha_dummy_113 x y)),
        ((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
        ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
        ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
        ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
        ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.all (nb063_alpha_dummy_086) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (nb063_alpha_dummy_086)) (Class.cv (nb063_alpha_dummy_079)))
            (Wff.classEq (Class.cv (nb063_alpha_dummy_087))
              (syn_cif (Wff.classMem (Class.cv (nb063_alpha_dummy_086)) (syn_cnnc))
                (syn_cplc (Class.cv (nb063_alpha_dummy_086)) (syn_c1c))
                (Class.cv (nb063_alpha_dummy_086)))))))
      (Wff.all (nb063_alpha_dummy_088 x y) (Wff.neg (syn_wa
            (Wff.classMem (Class.cv (nb063_alpha_dummy_088 x y))
              (Class.cv (nb063_alpha_dummy_081 x y)))
            (Wff.classEq (Class.cv (nb063_alpha_dummy_089 x y))
              (syn_cif (Wff.classMem (Class.cv (nb063_alpha_dummy_088 x y)) (syn_cnnc))
                (syn_cplc (Class.cv (nb063_alpha_dummy_088 x y)) (syn_c1c))
                (Class.cv (nb063_alpha_dummy_088 x y))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0086) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0087 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0086) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0087 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0116) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0117 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0114) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0115 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_079))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb063_alpha_dummy_081 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0090) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb063_support_mem_0091 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0090) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb063_support_mem_0091 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0088) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb063_alpha_dummy_094), (nb063_alpha_dummy_097 x y)),
                                    ((nb063_alpha_dummy_093), (nb063_alpha_dummy_096 x y)),
                                    ((nb063_alpha_dummy_092), (nb063_alpha_dummy_095 x y)),
                                    ((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
                                    ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
                                    ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
                                    ((nb063_alpha_dummy_112), (nb063_alpha_dummy_113 x y)),
                                    ((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
                                    ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                                    ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                                    ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
                                    ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                                    ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                                    ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                                    ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb063_split_alpha_0012 x y r a))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0088) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
                        ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
                        ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
                        ((nb063_alpha_dummy_112), (nb063_alpha_dummy_113 x y)),
                        ((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
                        ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                        ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                        ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
                        ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0088) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0088) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0089 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb063_alpha_dummy_090), (nb063_alpha_dummy_091 x y)),
                        ((nb063_alpha_dummy_086), (nb063_alpha_dummy_088 x y)),
                        ((nb063_alpha_dummy_087), (nb063_alpha_dummy_089 x y)),
                        ((nb063_alpha_dummy_112), (nb063_alpha_dummy_113 x y)),
                        ((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
                        ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                        ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                        ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
                        ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def nb063_split_alpha_0014 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
        ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
        ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
        ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
      (Wff.classMem (Class.cv (nb063_alpha_dummy_082)) (syn_ccompl
          (Class.cab (nb063_alpha_dummy_078)
            (syn_wrex (nb063_alpha_dummy_079) (Class.cv (nb063_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb063_alpha_dummy_078))
                (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_079))) (syn_csn (syn_c0c))))))))
      (Wff.classMem (Class.cv (nb063_alpha_dummy_083 x y)) (syn_ccompl
          (Class.cab (nb063_alpha_dummy_080 x y)
            (syn_wrex (nb063_alpha_dummy_081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb063_alpha_dummy_080 x y))
                (syn_cun (syn_cphi (Class.cv (nb063_alpha_dummy_081 x y)))
                  (syn_csn (syn_c0c)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 1))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0113 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0109) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0111 x y) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                                (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb063_alpha_dummy_003))).fv ∪
                            ((Class.cv (nb063_alpha_dummy_002))).fv) (by decide))
                        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (nb063_split_alpha_0013 x y r a))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (nb063_split_alpha_0013 x y r a))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
                                ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                                ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                                ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
                                ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                                ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                                ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                                ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                              (syn_ccompl (syn_csn (syn_c0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 1))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0108) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0110 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0113 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0109) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb063_support_mem_0111 x y) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                                (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb063_alpha_dummy_003))).fv ∪
                            ((Class.cv (nb063_alpha_dummy_002))).fv) (by decide))
                        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (nb063_split_alpha_0013 x y r a))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (nb063_split_alpha_0013 x y r a))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_closed
                              [((nb063_alpha_dummy_110), (nb063_alpha_dummy_111 x y)),
                                ((nb063_alpha_dummy_079), (nb063_alpha_dummy_081 x y)),
                                ((nb063_alpha_dummy_078), (nb063_alpha_dummy_080 x y)),
                                ((nb063_alpha_dummy_108), (nb063_alpha_dummy_109 x y)),
                                ((nb063_alpha_dummy_082), (nb063_alpha_dummy_083 x y)),
                                ((nb063_alpha_dummy_003), y), ((nb063_alpha_dummy_002), x),
                                ((nb063_alpha_dummy_000), a), ((nb063_alpha_dummy_001), r),
                                ((nb063_alpha_dummy_004), (nb063_alpha_dummy_005 x y r a))]
                              (syn_ccompl (syn_csn (syn_c0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))))))

@[expose]
noncomputable def nominal_df_connex (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cconnex) (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a)
              (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
                (syn_wbr (.cv y) (.cv r) (.cv x))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb063_split_alpha_0004 x y r a dv_a_r) (TAlphaWff.all
                (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_x
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.imp (TAlphaWff.neg
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb063_split_alpha_0009 x y r a dv_x_y))))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))
                        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb063_split_alpha_0011 x y r a))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb063_split_alpha_0011 x y r a))))))))) (nb063_split_alpha_0014 x y r a dv_x_y))))
                          (TAlphaClass.cv (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
