/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C061C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C061C001Part003`. -/


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
noncomputable def nb061_split_alpha_0000 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_021), (nb061_alpha_dummy_024 r a)),
        ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
        ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)),
        ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
        ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
        ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
        ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
        ((nb061_alpha_dummy_011), (nb061_alpha_dummy_012 r a)),
        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
        ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_019))
            (syn_cun (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_022 r a))
            (syn_cun (Class.cv (nb061_alpha_dummy_023 r a))
              (Class.cv (nb061_alpha_dummy_024 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb061_alpha_dummy_021), (nb061_alpha_dummy_024 r a)),
          ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
          ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)),
          ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
          ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
          ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
          ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
          ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
          ((nb061_alpha_dummy_011), (nb061_alpha_dummy_012 r a)),
          ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
          ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
          ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0001 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
        ((nb061_alpha_dummy_011), (nb061_alpha_dummy_012 r a)),
        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
        ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_006))
          (Class.cv (nb061_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_005))
            (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_008 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_007 r a))
            (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb061_alpha_dummy_001))).fv ∪
                ((Class.cv (nb061_alpha_dummy_000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_021),
        (nb061_alpha_dummy_024 r a)), ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
        ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)), ((nb061_alpha_dummy_017),
        (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
        ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_006),
        (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
        ((nb061_alpha_dummy_011), (nb061_alpha_dummy_012 r a)), ((nb061_alpha_dummy_009),
        (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb061_split_alpha_0000 x r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                              ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                              ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                              ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                              ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                              ((nb061_alpha_dummy_011), (nb061_alpha_dummy_012 r a)),
                              ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                              ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
                              ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                              ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                              ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                              ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                              ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                              ((nb061_alpha_dummy_011), (nb061_alpha_dummy_012 r a)),
                              ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                              ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
                              ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0002 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_021), (nb061_alpha_dummy_024 r a)),
        ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
        ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)),
        ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
        ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
        ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
        ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
        ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
        ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
        ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
        ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_019))
            (syn_cun (Class.cv (nb061_alpha_dummy_020)) (Class.cv (nb061_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb061_alpha_dummy_023 r a))
            (Class.cv (nb061_alpha_dummy_024 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_022 r a))
            (syn_cun (Class.cv (nb061_alpha_dummy_023 r a))
              (Class.cv (nb061_alpha_dummy_024 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb061_alpha_dummy_021), (nb061_alpha_dummy_024 r a)),
          ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
          ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)),
          ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
          ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
          ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
          ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
          ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
          ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
          ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
          ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
          ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
          ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
          ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_015 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C061C001Part004`. -/


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
noncomputable def nb061_split_alpha_0003 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
        ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
        ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
        ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
        ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_039))
          (syn_cphi (Class.cv (nb061_alpha_dummy_006)))) (Wff.neg
          (Wff.classMem (Class.cv (nb061_alpha_dummy_039))
            (syn_cphi (Class.cv (nb061_alpha_dummy_006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_040 r a))
          (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb061_alpha_dummy_040 r a))
            (syn_cphi (Class.cv (nb061_alpha_dummy_008 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_021),
        (nb061_alpha_dummy_024 r a)), ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
                                        ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)),
                                        ((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                                        ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                                        ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                                        ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
                                        ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
                                        ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                                        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                                        ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                                        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                                        ((nb061_alpha_dummy_000), a),
                                        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003),
        (nb061_alpha_dummy_004 x r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb061_split_alpha_0002 x r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                            ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                            ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                            ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
                            ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
                            ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                            ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                            ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                            ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                            ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
                            ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                            ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                            ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                            ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
                            ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
                            ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                            ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                            ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                            ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                            ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
                            ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb061_alpha_dummy_008 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_021),
        (nb061_alpha_dummy_024 r a)), ((nb061_alpha_dummy_020), (nb061_alpha_dummy_023 r a)),
        ((nb061_alpha_dummy_019), (nb061_alpha_dummy_022 r a)), ((nb061_alpha_dummy_017),
        (nb061_alpha_dummy_018 r a)), ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
        ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)), ((nb061_alpha_dummy_039),
        (nb061_alpha_dummy_040 r a)), ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
        ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)), ((nb061_alpha_dummy_005),
        (nb061_alpha_dummy_007 r a)), ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb061_split_alpha_0002 x r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                              ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                              ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                              ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
                              ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
                              ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                              ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                              ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                              ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                              ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
                              ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb061_alpha_dummy_017), (nb061_alpha_dummy_018 r a)),
                              ((nb061_alpha_dummy_013), (nb061_alpha_dummy_015 r a)),
                              ((nb061_alpha_dummy_014), (nb061_alpha_dummy_016 r a)),
                              ((nb061_alpha_dummy_039), (nb061_alpha_dummy_040 r a)),
                              ((nb061_alpha_dummy_037), (nb061_alpha_dummy_038 r a)),
                              ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                              ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                              ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                              ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                              ((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
                              ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0004 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb061_alpha_dummy_000), a), ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.classEq (Class.cv (nb061_alpha_dummy_003))
        (syn_cop (Class.cv (nb061_alpha_dummy_001)) (Class.cv (nb061_alpha_dummy_000))))
      (Wff.classEq (Class.cv (nb061_alpha_dummy_004 x r a))
        (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0002) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0003 x r a) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0000) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0001 x r a) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061_split_alpha_0001 x r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061_split_alpha_0001 x r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb061_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb061_split_alpha_0003 x r a)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_037),
        (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                                        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                                        ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                                        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                                        ((nb061_alpha_dummy_000), a),
                                        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003),
        (nb061_alpha_dummy_004 x r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb061_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb061_split_alpha_0003 x r a)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_037),
        (nb061_alpha_dummy_038 r a)), ((nb061_alpha_dummy_006), (nb061_alpha_dummy_008 r a)),
                                        ((nb061_alpha_dummy_005), (nb061_alpha_dummy_007 r a)),
                                        ((nb061_alpha_dummy_035), (nb061_alpha_dummy_036 r a)),
                                        ((nb061_alpha_dummy_009), (nb061_alpha_dummy_010 r a)),
                                        ((nb061_alpha_dummy_000), a),
                                        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003),
        (nb061_alpha_dummy_004 x r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0005 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)),
        ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)),
        ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)),
        ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
        ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
        ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
        ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
        ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
        ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)),
        ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
        ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_055))
            (syn_cun (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_058 x))
            (syn_cun (Class.cv (nb061_alpha_dummy_059 x))
              (Class.cv (nb061_alpha_dummy_060 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)),
          ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)),
          ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)),
          ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
          ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
          ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
          ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
          ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
          ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)),
          ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
          ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
          ((nb061_alpha_dummy_001), r),
          ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0006 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
        ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
        ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)),
        ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
        ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_042))
          (Class.cv (nb061_alpha_dummy_002))) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_041))
            (syn_cphi (Class.cv (nb061_alpha_dummy_042))))))
      (Wff.imp (Wff.classMem (Class.cv (nb061_alpha_dummy_044 x)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_043 x))
            (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0047 x) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0045 x) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_002))).fv ∪
                ((Class.cv (nb061_alpha_dummy_002))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb061_alpha_dummy_042))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb061_alpha_dummy_044 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0053 x) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0051 x) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_057),
        (nb061_alpha_dummy_060 x)), ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)),
        ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)), ((nb061_alpha_dummy_053),
        (nb061_alpha_dummy_054 x)), ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
        ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)), ((nb061_alpha_dummy_042),
        (nb061_alpha_dummy_044 x)), ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
        ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)), ((nb061_alpha_dummy_045),
        (nb061_alpha_dummy_046 x)), ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb061_split_alpha_0005 x r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
                              ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
                              ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
                              ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                              ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                              ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)),
                              ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                              ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
                              ((nb061_alpha_dummy_001), r),
                              ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
                              ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
                              ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
                              ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                              ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                              ((nb061_alpha_dummy_047), (nb061_alpha_dummy_048 x)),
                              ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                              ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
                              ((nb061_alpha_dummy_001), r),
                              ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C061C001Part005`. -/


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
noncomputable def nb061_split_alpha_0007 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)),
        ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)),
        ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)),
        ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
        ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
        ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
        ((nb061_alpha_dummy_075), (nb061_alpha_dummy_076 x)),
        ((nb061_alpha_dummy_073), (nb061_alpha_dummy_074 x)),
        ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
        ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
        ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
        ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
        ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb061_alpha_dummy_055))
            (syn_cun (Class.cv (nb061_alpha_dummy_056)) (Class.cv (nb061_alpha_dummy_057))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb061_alpha_dummy_059 x))
            (Class.cv (nb061_alpha_dummy_060 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061_alpha_dummy_058 x))
            (syn_cun (Class.cv (nb061_alpha_dummy_059 x))
              (Class.cv (nb061_alpha_dummy_060 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)),
          ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)),
          ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)),
          ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
          ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
          ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
          ((nb061_alpha_dummy_075), (nb061_alpha_dummy_076 x)),
          ((nb061_alpha_dummy_073), (nb061_alpha_dummy_074 x)),
          ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
          ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
          ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
          ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
          ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
          ((nb061_alpha_dummy_001), r),
          ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_049))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_051 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0008 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061_alpha_dummy_075), (nb061_alpha_dummy_076 x)),
        ((nb061_alpha_dummy_073), (nb061_alpha_dummy_074 x)),
        ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
        ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
        ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
        ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
        ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.classMem (Class.cv (nb061_alpha_dummy_075))
        (syn_cphi (Class.cv (nb061_alpha_dummy_042))))
      (Wff.classMem (Class.cv (nb061_alpha_dummy_076 x))
        (syn_cphi (Class.cv (nb061_alpha_dummy_044 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0074) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0075 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0072) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0073 x) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb061_alpha_dummy_042))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb061_alpha_dummy_044 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0052) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0053 x) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0052) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0053 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0050) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb061_alpha_dummy_057), (nb061_alpha_dummy_060 x)),
                                      ((nb061_alpha_dummy_056), (nb061_alpha_dummy_059 x)),
                                      ((nb061_alpha_dummy_055), (nb061_alpha_dummy_058 x)),
                                      ((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
                                      ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
                                      ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
                                      ((nb061_alpha_dummy_075), (nb061_alpha_dummy_076 x)),
                                      ((nb061_alpha_dummy_073), (nb061_alpha_dummy_074 x)),
                                      ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                                      ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                                      ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
                                      ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                                      ((nb061_alpha_dummy_002), x),
                                      ((nb061_alpha_dummy_000), a),
                                      ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003),
                                        (nb061_alpha_dummy_004 x r a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb061_split_alpha_0007 x r a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
                          ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
                          ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
                          ((nb061_alpha_dummy_075), (nb061_alpha_dummy_076 x)),
                          ((nb061_alpha_dummy_073), (nb061_alpha_dummy_074 x)),
                          ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                          ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                          ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
                          ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                          ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
                          ((nb061_alpha_dummy_001), r),
                          ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb061_alpha_dummy_053), (nb061_alpha_dummy_054 x)),
                          ((nb061_alpha_dummy_049), (nb061_alpha_dummy_051 x)),
                          ((nb061_alpha_dummy_050), (nb061_alpha_dummy_052 x)),
                          ((nb061_alpha_dummy_075), (nb061_alpha_dummy_076 x)),
                          ((nb061_alpha_dummy_073), (nb061_alpha_dummy_074 x)),
                          ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                          ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                          ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
                          ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                          ((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
                          ((nb061_alpha_dummy_001), r),
                          ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb061_split_alpha_0009 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r)
    (dv_r_x : r ≠ x) :
    TAlphaWff
      [((nb061_alpha_dummy_002), x), ((nb061_alpha_dummy_000), a),
        ((nb061_alpha_dummy_001), r),
        ((nb061_alpha_dummy_003), (nb061_alpha_dummy_004 x r a))]
      (Wff.classMem
        (syn_cop (Class.cv (nb061_alpha_dummy_002)) (Class.cv (nb061_alpha_dummy_002)))
        (Class.cv (nb061_alpha_dummy_001)))
      (Wff.classMem (syn_cop (Class.cv x) (Class.cv x)) (Class.cv r)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061_split_alpha_0006 x r a)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061_split_alpha_0006 x r a)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0042) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0042) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0070) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0071 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0043) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0045 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_002))).fv ∪
                                    ((Class.cv (nb061_alpha_dummy_002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (nb061_split_alpha_0008 x r a)
        (nb061_split_alpha_0008 x r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_073),
        (nb061_alpha_dummy_074 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                                        ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                                        ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
                                        ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                                        ((nb061_alpha_dummy_002), x),
                                        ((nb061_alpha_dummy_000), a),
                                        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003),
        (nb061_alpha_dummy_004 x r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0042) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0042) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0070) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0071 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0043) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0045 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061_alpha_dummy_002))).fv ∪
                                    ((Class.cv (nb061_alpha_dummy_002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (nb061_split_alpha_0008 x r a)
        (nb061_split_alpha_0008 x r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb061_alpha_dummy_073),
        (nb061_alpha_dummy_074 x)), ((nb061_alpha_dummy_042), (nb061_alpha_dummy_044 x)),
                                        ((nb061_alpha_dummy_041), (nb061_alpha_dummy_043 x)),
                                        ((nb061_alpha_dummy_071), (nb061_alpha_dummy_072 x)),
                                        ((nb061_alpha_dummy_045), (nb061_alpha_dummy_046 x)),
                                        ((nb061_alpha_dummy_002), x),
                                        ((nb061_alpha_dummy_000), a),
                                        ((nb061_alpha_dummy_001), r), ((nb061_alpha_dummy_003),
        (nb061_alpha_dummy_004 x r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv
      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
          (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))

@[expose]
noncomputable def nominal_df_ref (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r)
    (dv_a_x : a ≠ x) (dv_r_x : r ≠ x) :
    Nominal.NPrf
      (.classEq (syn_cref)
        (syn_copab r a (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb061_split_alpha_0004 x r a dv_a_r) (TAlphaWff.all (TAlphaWff.imp
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.here _ _ _))))
                  (nb061_split_alpha_0009 x r a dv_a_r dv_r_x)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
