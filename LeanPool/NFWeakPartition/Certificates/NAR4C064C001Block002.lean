/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C064C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C064C001Part003`. -/


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
noncomputable def nb064_split_alpha_0000 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)),
        ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
        ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)),
        ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
        ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
        ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
        ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
        ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)),
        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
        ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_021))
            (syn_cun (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_025 r a))
            (Class.cv (nb064_alpha_dummy_026 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_024 r a))
            (syn_cun (Class.cv (nb064_alpha_dummy_025 r a))
              (Class.cv (nb064_alpha_dummy_026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)),
          ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
          ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)),
          ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
          ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
          ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
          ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
          ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
          ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)),
          ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
          ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
          ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb064_split_alpha_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
        ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)),
        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
        ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_008))
          (Class.cv (nb064_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_007))
            (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_010 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_009 r a))
            (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb064_alpha_dummy_001))).fv ∪
                ((Class.cv (nb064_alpha_dummy_000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb064_alpha_dummy_023),
        (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
        ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019),
        (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
        ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_008),
        (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
        ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)), ((nb064_alpha_dummy_011),
        (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
        (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb064_split_alpha_0000 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                              ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                              ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                              ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                              ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                              ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)),
                              ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                              ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
                              ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                              ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                              ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                              ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                              ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                              ((nb064_alpha_dummy_013), (nb064_alpha_dummy_014 r a)),
                              ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                              ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
                              ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb064_split_alpha_0002 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)),
        ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
        ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)),
        ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
        ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
        ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
        ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
        ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
        ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
        ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
        ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_021))
            (syn_cun (Class.cv (nb064_alpha_dummy_022)) (Class.cv (nb064_alpha_dummy_023))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_025 r a))
            (Class.cv (nb064_alpha_dummy_026 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_024 r a))
            (syn_cun (Class.cv (nb064_alpha_dummy_025 r a))
              (Class.cv (nb064_alpha_dummy_026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb064_alpha_dummy_023), (nb064_alpha_dummy_026 r a)),
          ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
          ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)),
          ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
          ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
          ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
          ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
          ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
          ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
          ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
          ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
          ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
          ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
          ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C064C001Part004`. -/


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
noncomputable def nb064_split_alpha_0003 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
        ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
        ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
        ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
        ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_041))
          (syn_cphi (Class.cv (nb064_alpha_dummy_008)))) (Wff.neg
          (Wff.classMem (Class.cv (nb064_alpha_dummy_041))
            (syn_cphi (Class.cv (nb064_alpha_dummy_008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_042 r a))
          (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb064_alpha_dummy_042 r a))
            (syn_cphi (Class.cv (nb064_alpha_dummy_010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb064_alpha_dummy_023),
        (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
                                        ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)),
                                        ((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                                        ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                                        ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                                        ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
                                        ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
                                        ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                                        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                                        ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                                        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                                        ((nb064_alpha_dummy_000), a),
                                        ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
        (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb064_split_alpha_0002 x y z r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                            ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                            ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                            ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
                            ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
                            ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                            ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                            ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                            ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                            ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
                            ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                            ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                            ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                            ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
                            ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
                            ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                            ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                            ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                            ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                            ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
                            ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb064_alpha_dummy_010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb064_alpha_dummy_023),
        (nb064_alpha_dummy_026 r a)), ((nb064_alpha_dummy_022), (nb064_alpha_dummy_025 r a)),
        ((nb064_alpha_dummy_021), (nb064_alpha_dummy_024 r a)), ((nb064_alpha_dummy_019),
        (nb064_alpha_dummy_020 r a)), ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
        ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)), ((nb064_alpha_dummy_041),
        (nb064_alpha_dummy_042 r a)), ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
        ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)), ((nb064_alpha_dummy_007),
        (nb064_alpha_dummy_009 r a)), ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
        (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb064_split_alpha_0002 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                              ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                              ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                              ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
                              ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
                              ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                              ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                              ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                              ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                              ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
                              ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb064_alpha_dummy_019), (nb064_alpha_dummy_020 r a)),
                              ((nb064_alpha_dummy_015), (nb064_alpha_dummy_017 r a)),
                              ((nb064_alpha_dummy_016), (nb064_alpha_dummy_018 r a)),
                              ((nb064_alpha_dummy_041), (nb064_alpha_dummy_042 r a)),
                              ((nb064_alpha_dummy_039), (nb064_alpha_dummy_040 r a)),
                              ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                              ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                              ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                              ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                              ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
                              ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb064_pair_occurrence (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaClass
      [((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Class.cv (nb064_alpha_dummy_005)) (Class.cv (nb064_alpha_dummy_006 x y z r a)) :=
  by
  have freshness0 : (nb064_alpha_dummy_005) ≠ (nb064_alpha_dummy_000) :=
    by
    unfold nb064_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0002) 0)))
  have freshness1 : (nb064_alpha_dummy_006 x y z r a) ≠ a :=
    by
    unfold nb064_alpha_dummy_006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0003 x y z r a) 0)))
  have freshness2 : (nb064_alpha_dummy_005) ≠ (nb064_alpha_dummy_001) :=
    by
    unfold nb064_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0000) 0)))
  have freshness3 : (nb064_alpha_dummy_006 x y z r a) ≠ r :=
    by
    unfold nb064_alpha_dummy_006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0001 x y z r a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb064_split_alpha_0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.classEq (Class.cv (nb064_alpha_dummy_005))
        (syn_cop (Class.cv (nb064_alpha_dummy_001)) (Class.cv (nb064_alpha_dummy_000))))
      (Wff.classEq (Class.cv (nb064_alpha_dummy_006 x y z r a))
        (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (nb064_pair_occurrence x y z r a) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb064_split_alpha_0001 x y z r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb064_split_alpha_0001 x y z r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb064_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb064_split_alpha_0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb064_alpha_dummy_039),
        (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                                        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                                        ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                                        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                                        ((nb064_alpha_dummy_000), a),
                                        ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
        (nb064_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb064_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb064_split_alpha_0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb064_alpha_dummy_039),
        (nb064_alpha_dummy_040 r a)), ((nb064_alpha_dummy_008), (nb064_alpha_dummy_010 r a)),
                                        ((nb064_alpha_dummy_007), (nb064_alpha_dummy_009 r a)),
                                        ((nb064_alpha_dummy_037), (nb064_alpha_dummy_038 r a)),
                                        ((nb064_alpha_dummy_011), (nb064_alpha_dummy_012 r a)),
                                        ((nb064_alpha_dummy_000), a),
                                        ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
        (nb064_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nb064_split_alpha_0005 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)),
        ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)),
        ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)),
        ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
        ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
        ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
        ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
        ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
        ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)),
        ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
        ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
        ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_061))
            (syn_cun (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_065 y z))
            (Class.cv (nb064_alpha_dummy_066 y z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_064 y z))
            (syn_cun (Class.cv (nb064_alpha_dummy_065 y z))
              (Class.cv (nb064_alpha_dummy_066 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)),
          ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)),
          ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)),
          ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
          ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
          ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
          ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
          ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
          ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)),
          ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
          ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
          ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
          ((nb064_alpha_dummy_001), r),
          ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C064C001Part005`. -/


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
noncomputable def nb064_split_alpha_0006 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
        ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
        ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)),
        ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
        ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
        ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_048))
          (Class.cv (nb064_alpha_dummy_003))) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_047))
            (syn_cphi (Class.cv (nb064_alpha_dummy_048))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_050 y z)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z))
            (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0054) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0055 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0051) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0053 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_003))).fv ∪
                ((Class.cv (nb064_alpha_dummy_004))).fv) (by decide))
            (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb064_alpha_dummy_048))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb064_alpha_dummy_050 y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0060) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0061 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0060) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0061 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0058) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0059 y z) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb064_alpha_dummy_063),
        (nb064_alpha_dummy_066 y z)), ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)),
        ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)), ((nb064_alpha_dummy_059),
        (nb064_alpha_dummy_060 y z)), ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
        ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)), ((nb064_alpha_dummy_048),
        (nb064_alpha_dummy_050 y z)), ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
        ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)), ((nb064_alpha_dummy_051),
        (nb064_alpha_dummy_052 y z)), ((nb064_alpha_dummy_003), y),
        ((nb064_alpha_dummy_004), z), ((nb064_alpha_dummy_002), x),
        ((nb064_alpha_dummy_000), a), ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
        (nb064_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb064_split_alpha_0005 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
                              ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
                              ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
                              ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                              ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                              ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)),
                              ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                              ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                              ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                              ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
                                (nb064_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
                              ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
                              ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
                              ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                              ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                              ((nb064_alpha_dummy_053), (nb064_alpha_dummy_054 y z)),
                              ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                              ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                              ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                              ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
                                (nb064_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb064_split_alpha_0007 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)),
        ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)),
        ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)),
        ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
        ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
        ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
        ((nb064_alpha_dummy_081), (nb064_alpha_dummy_082 y z)),
        ((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
        ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
        ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
        ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
        ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
        ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
        ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb064_alpha_dummy_061))
            (syn_cun (Class.cv (nb064_alpha_dummy_062)) (Class.cv (nb064_alpha_dummy_063))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb064_alpha_dummy_065 y z))
            (Class.cv (nb064_alpha_dummy_066 y z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_064 y z))
            (syn_cun (Class.cv (nb064_alpha_dummy_065 y z))
              (Class.cv (nb064_alpha_dummy_066 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)),
          ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)),
          ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)),
          ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
          ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
          ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
          ((nb064_alpha_dummy_081), (nb064_alpha_dummy_082 y z)),
          ((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
          ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
          ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
          ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
          ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
          ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
          ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
          ((nb064_alpha_dummy_001), r),
          ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_055))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064_alpha_dummy_057 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb064_split_alpha_0008 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
        ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
        ((nb064_alpha_dummy_081), (nb064_alpha_dummy_082 y z)),
        ((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
        ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
        ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
        ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
        ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
        ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
        ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_055))
          (Class.cv (nb064_alpha_dummy_048))) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_056))
            (syn_cif (Wff.classMem (Class.cv (nb064_alpha_dummy_055)) (syn_cnnc))
              (syn_cplc (Class.cv (nb064_alpha_dummy_055)) (syn_c1c))
              (Class.cv (nb064_alpha_dummy_055))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_057 y z))
          (Class.cv (nb064_alpha_dummy_050 y z))) (Wff.neg
          (Wff.classEq (Class.cv (nb064_alpha_dummy_058 y z))
            (syn_cif (Wff.classMem (Class.cv (nb064_alpha_dummy_057 y z)) (syn_cnnc))
              (syn_cplc (Class.cv (nb064_alpha_dummy_057 y z)) (syn_c1c))
              (Class.cv (nb064_alpha_dummy_057 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0086) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0087 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0084) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0085 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064_alpha_dummy_048))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb064_alpha_dummy_050 y z))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0060) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0061 y z) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0060) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0061 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0058) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb064_alpha_dummy_063), (nb064_alpha_dummy_066 y z)),
                                  ((nb064_alpha_dummy_062), (nb064_alpha_dummy_065 y z)),
                                  ((nb064_alpha_dummy_061), (nb064_alpha_dummy_064 y z)),
                                  ((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
                                  ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
                                  ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
                                  ((nb064_alpha_dummy_081), (nb064_alpha_dummy_082 y z)),
                                  ((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
                                  ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                                  ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                                  ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
                                  ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                                  ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                                  ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                                  ((nb064_alpha_dummy_001), r), ((nb064_alpha_dummy_005),
                                    (nb064_alpha_dummy_006 x y z r a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb064_split_alpha_0007 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
                      ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
                      ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
                      ((nb064_alpha_dummy_081), (nb064_alpha_dummy_082 y z)),
                      ((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
                      ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                      ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                      ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
                      ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                      ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                      ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                      ((nb064_alpha_dummy_001), r),
                      ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb064_alpha_dummy_059), (nb064_alpha_dummy_060 y z)),
                      ((nb064_alpha_dummy_055), (nb064_alpha_dummy_057 y z)),
                      ((nb064_alpha_dummy_056), (nb064_alpha_dummy_058 y z)),
                      ((nb064_alpha_dummy_081), (nb064_alpha_dummy_082 y z)),
                      ((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
                      ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                      ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                      ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
                      ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                      ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                      ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                      ((nb064_alpha_dummy_001), r),
                      ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb064_split_alpha_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
        ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
        ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
        ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
        ((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_077))
          (Class.cab (nb064_alpha_dummy_047)
            (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb064_alpha_dummy_047))
                (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb064_alpha_dummy_077))
            (Class.cab (nb064_alpha_dummy_047)
              (syn_wrex (nb064_alpha_dummy_048) (Class.cv (nb064_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb064_alpha_dummy_047))
                  (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_048)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064_alpha_dummy_078 y z))
          (Class.cab (nb064_alpha_dummy_049 y z)
            (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z))
                (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb064_alpha_dummy_078 y z))
            (Class.cab (nb064_alpha_dummy_049 y z)
              (syn_wrex (nb064_alpha_dummy_050 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb064_alpha_dummy_049 y z))
                  (syn_cun (syn_cphi (Class.cv (nb064_alpha_dummy_050 y z)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0082) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0083 y z) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0079) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0081 y z) 0))
                        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_y_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb064_alpha_dummy_003))).fv ∪
                      ((Class.cv (nb064_alpha_dummy_004))).fv) (by decide))
                  (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb064_split_alpha_0008 x y z r a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                    (nb064_split_alpha_0008 x y z r a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
                          ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                          ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                          ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
                          ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                          ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                          ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                          ((nb064_alpha_dummy_001), r),
                          ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0082) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0083 y z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0079) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0081 y z) 0))
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (Ne.symm dv_y_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb064_alpha_dummy_003))).fv ∪
                        ((Class.cv (nb064_alpha_dummy_004))).fv) (by decide))
                    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb064_split_alpha_0008 x y z r a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb064_split_alpha_0008 x y z r a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb064_alpha_dummy_079), (nb064_alpha_dummy_080 y z)),
                            ((nb064_alpha_dummy_048), (nb064_alpha_dummy_050 y z)),
                            ((nb064_alpha_dummy_047), (nb064_alpha_dummy_049 y z)),
                            ((nb064_alpha_dummy_077), (nb064_alpha_dummy_078 y z)),
                            ((nb064_alpha_dummy_051), (nb064_alpha_dummy_052 y z)),
                            ((nb064_alpha_dummy_003), y), ((nb064_alpha_dummy_004), z),
                            ((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                            ((nb064_alpha_dummy_001), r),
                            ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb064_split_alpha_0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (dv_r_z : r ≠ z)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb064_alpha_dummy_001), r),
        ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
      (Wff.all (nb064_alpha_dummy_000) (Wff.neg (syn_wa
            (Wff.classEq (Class.cv (nb064_alpha_dummy_005))
              (syn_cop (Class.cv (nb064_alpha_dummy_001)) (Class.cv (nb064_alpha_dummy_000))))
            (Wff.all (nb064_alpha_dummy_002) (Wff.imp (syn_wa
                  (syn_wss (Class.cv (nb064_alpha_dummy_002))
                    (Class.cv (nb064_alpha_dummy_000)))
                  (syn_wne (Class.cv (nb064_alpha_dummy_002)) (syn_c0)))
                (syn_wrex (nb064_alpha_dummy_004) (Class.cv (nb064_alpha_dummy_002))
                  (syn_wral (nb064_alpha_dummy_003) (Class.cv (nb064_alpha_dummy_002)) (Wff.imp
                      (syn_wbr (Class.cv (nb064_alpha_dummy_003))
                        (Class.cv (nb064_alpha_dummy_001)) (Class.cv (nb064_alpha_dummy_004)))
                      (Wff.objEq (nb064_alpha_dummy_003) (nb064_alpha_dummy_004))))))))))
      (Wff.all a (Wff.neg (syn_wa (Wff.classEq (Class.cv (nb064_alpha_dummy_006 x y z r a))
              (syn_cop (Class.cv r) (Class.cv a))) (Wff.all x (Wff.imp
                (syn_wa (syn_wss (Class.cv x) (Class.cv a)) (syn_wne (Class.cv x) (syn_c0)))
                (syn_wrex z (Class.cv x) (syn_wral y (Class.cv x)
                    (Wff.imp (syn_wbr (Class.cv y) (Class.cv r) (Class.cv z))
                      (Wff.objEq y z))))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (nb064_split_alpha_0004 x y z r a dv_a_r)
        (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0044) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0045 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0042) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0043 x a) 0))
                                      (TAlphaVar.here _ _ _)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0048) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0049 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0046) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0047 x a) 0))
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_a_x (TAlphaVar.here _ _ _))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0044) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0045 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0042) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0043 x a) 0))
                                      (TAlphaVar.here _ _ _)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0048) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0049 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0046) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0047 x a) 0))
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_a_x (TAlphaVar.here _ _ _)))))))))))))
                (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_closed
                    [((nb064_alpha_dummy_002), x), ((nb064_alpha_dummy_000), a),
                      ((nb064_alpha_dummy_001), r),
                      ((nb064_alpha_dummy_005), (nb064_alpha_dummy_006 x y z r a))]
                    (syn_c0) (by simp only [fv_syn_c0]))))) (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      dv_x_z (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.imp (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb064_split_alpha_0006 x y z r a))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb064_split_alpha_0006 x y z r a)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb064_split_alpha_0009 x y z r a dv_y_z))))))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_y_z) (TAlphaVar.here _ _ _)))))))))))))

@[expose]
noncomputable def nominal_df_found (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (__dv_a_y : a ≠ y) (__dv_a_z : a ≠ z)
    (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (dv_r_z : r ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cfound) (syn_copab r a (.all x
            (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
              (syn_wrex z (.cv x) (syn_wral y (.cv x)
                  (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
            (nb064_split_alpha_0010 x y z r a dv_a_r dv_a_x dv_r_x dv_r_y dv_r_z dv_x_y
              dv_x_z dv_y_z))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
