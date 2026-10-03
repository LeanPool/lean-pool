/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C060C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C060C001Part005`. -/


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
noncomputable def nb060_split_alpha_0000 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_023), (nb060_alpha_dummy_026 r a)),
        ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
        ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)),
        ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
        ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
        ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
        ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
        ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)),
        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_021))
            (syn_cun (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_024 r a))
            (syn_cun (Class.cv (nb060_alpha_dummy_025 r a))
              (Class.cv (nb060_alpha_dummy_026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_023), (nb060_alpha_dummy_026 r a)),
          ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
          ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)),
          ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
          ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
          ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
          ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
          ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
          ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)),
          ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
          ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
        ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)),
        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_008))
          (Class.cv (nb060_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_007))
            (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_010 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a))
            (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_001))).fv ∪
                ((Class.cv (nb060_alpha_dummy_000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060_alpha_dummy_010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_023),
        (nb060_alpha_dummy_026 r a)), ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
        ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)), ((nb060_alpha_dummy_019),
        (nb060_alpha_dummy_020 r a)), ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
        ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)), ((nb060_alpha_dummy_008),
        (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
        ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)), ((nb060_alpha_dummy_011),
        (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060_split_alpha_0000 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                              ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                              ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                              ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                              ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                              ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)),
                              ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                              ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
                              ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                              ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                              ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                              ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                              ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                              ((nb060_alpha_dummy_013), (nb060_alpha_dummy_014 r a)),
                              ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                              ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
                              ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0002 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_023), (nb060_alpha_dummy_026 r a)),
        ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
        ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)),
        ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
        ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
        ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
        ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
        ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
        ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
        ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_021))
            (syn_cun (Class.cv (nb060_alpha_dummy_022)) (Class.cv (nb060_alpha_dummy_023))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_025 r a))
            (Class.cv (nb060_alpha_dummy_026 r a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_024 r a))
            (syn_cun (Class.cv (nb060_alpha_dummy_025 r a))
              (Class.cv (nb060_alpha_dummy_026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_023), (nb060_alpha_dummy_026 r a)),
          ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
          ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)),
          ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
          ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
          ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
          ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
          ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
          ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
          ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
          ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
          ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
          ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0003 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
        ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
        ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
        ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_041))
          (syn_cphi (Class.cv (nb060_alpha_dummy_008)))) (Wff.neg
          (Wff.classMem (Class.cv (nb060_alpha_dummy_041))
            (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_042 r a))
          (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb060_alpha_dummy_042 r a))
            (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_008))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb060_alpha_dummy_010 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_023),
        (nb060_alpha_dummy_026 r a)), ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
                                        ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)),
                                        ((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                                        ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                                        ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                                        ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
                                        ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
                                        ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                                        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                                        ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                                        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                                        ((nb060_alpha_dummy_000), a),
                                        ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb060_split_alpha_0002 x y z r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                            ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                            ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                            ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
                            ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
                            ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                            ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                            ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                            ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                            ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
                            ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                            ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                            ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                            ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
                            ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
                            ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                            ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                            ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                            ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                            ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
                            ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060_alpha_dummy_010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_023),
        (nb060_alpha_dummy_026 r a)), ((nb060_alpha_dummy_022), (nb060_alpha_dummy_025 r a)),
        ((nb060_alpha_dummy_021), (nb060_alpha_dummy_024 r a)), ((nb060_alpha_dummy_019),
        (nb060_alpha_dummy_020 r a)), ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
        ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)), ((nb060_alpha_dummy_041),
        (nb060_alpha_dummy_042 r a)), ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
        ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)), ((nb060_alpha_dummy_007),
        (nb060_alpha_dummy_009 r a)), ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060_split_alpha_0002 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                              ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                              ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                              ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
                              ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
                              ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                              ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                              ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                              ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                              ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
                              ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_019), (nb060_alpha_dummy_020 r a)),
                              ((nb060_alpha_dummy_015), (nb060_alpha_dummy_017 r a)),
                              ((nb060_alpha_dummy_016), (nb060_alpha_dummy_018 r a)),
                              ((nb060_alpha_dummy_041), (nb060_alpha_dummy_042 r a)),
                              ((nb060_alpha_dummy_039), (nb060_alpha_dummy_040 r a)),
                              ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                              ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                              ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                              ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                              ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
                              ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part006`. -/


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
noncomputable def nb060_ordered_pair_binder_occurrence (x : Var) (y : Var) (z : Var)
    (r : Var) (a : Var) :
    TAlphaClass
      [((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Class.cv (nb060_alpha_dummy_005)) (Class.cv (nb060_alpha_dummy_006 x y z r a)) :=
  by
  have freshness0 : (nb060_alpha_dummy_005) ≠ (nb060_alpha_dummy_000) :=
    by
    unfold nb060_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0002) 0)))
  have freshness1 : (nb060_alpha_dummy_006 x y z r a) ≠ a :=
    by
    unfold nb060_alpha_dummy_006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0003 x y z r a) 0)))
  have freshness2 : (nb060_alpha_dummy_005) ≠ (nb060_alpha_dummy_001) :=
    by
    unfold nb060_alpha_dummy_005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0000) 0)))
  have freshness3 : (nb060_alpha_dummy_006 x y z r a) ≠ r :=
    by
    unfold nb060_alpha_dummy_006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0001 x y z r a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb060_split_alpha_0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.classEq (Class.cv (nb060_alpha_dummy_005))
        (syn_cop (Class.cv (nb060_alpha_dummy_001)) (Class.cv (nb060_alpha_dummy_000))))
      (Wff.classEq (Class.cv (nb060_alpha_dummy_006 x y z r a))
        (syn_cop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (nb060_ordered_pair_binder_occurrence x y z r a) (TAlphaClass.cab
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb060_split_alpha_0001 x y z r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb060_split_alpha_0001 x y z r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb060_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb060_split_alpha_0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_039),
        (nb060_alpha_dummy_040 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                                        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                                        ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                                        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                                        ((nb060_alpha_dummy_000), a),
                                        ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb060_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb060_split_alpha_0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_039),
        (nb060_alpha_dummy_040 r a)), ((nb060_alpha_dummy_008), (nb060_alpha_dummy_010 r a)),
                                        ((nb060_alpha_dummy_007), (nb060_alpha_dummy_009 r a)),
                                        ((nb060_alpha_dummy_037), (nb060_alpha_dummy_038 r a)),
                                        ((nb060_alpha_dummy_011), (nb060_alpha_dummy_012 r a)),
                                        ((nb060_alpha_dummy_000), a),
                                        ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0005 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)),
        ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)),
        ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)),
        ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
        ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
        ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
        ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
        ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
        ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)),
        ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_057))
            (syn_cun (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_060 x y))
            (syn_cun (Class.cv (nb060_alpha_dummy_061 x y))
              (Class.cv (nb060_alpha_dummy_062 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)),
          ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)),
          ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)),
          ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
          ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
          ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
          ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
          ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
          ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)),
          ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
          ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    TAlphaWff
      [((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
        ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
        ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)),
        ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_044))
          (Class.cv (nb060_alpha_dummy_002))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
            (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_046 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
            (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0047 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0045 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_002))).fv ∪
                ((Class.cv (nb060_alpha_dummy_003))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_044))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060_alpha_dummy_046 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0053 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_059),
        (nb060_alpha_dummy_062 x y)), ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)),
        ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)), ((nb060_alpha_dummy_055),
        (nb060_alpha_dummy_056 x y)), ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
        ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)), ((nb060_alpha_dummy_044),
        (nb060_alpha_dummy_046 x y)), ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
        ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)), ((nb060_alpha_dummy_047),
        (nb060_alpha_dummy_048 x y)), ((nb060_alpha_dummy_004), z),
        ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060_split_alpha_0005 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
                              ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
                              ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
                              ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                              ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                              ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)),
                              ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
                              ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
                              ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
                              ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                              ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                              ((nb060_alpha_dummy_049), (nb060_alpha_dummy_050 x y)),
                              ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part007`. -/


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
noncomputable def nb060_split_alpha_0007 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)),
        ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)),
        ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)),
        ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
        ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
        ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
        ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)),
        ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
        ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
        ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
        ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
        ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_057))
            (syn_cun (Class.cv (nb060_alpha_dummy_058)) (Class.cv (nb060_alpha_dummy_059))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_061 x y))
            (Class.cv (nb060_alpha_dummy_062 x y))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_060 x y))
            (syn_cun (Class.cv (nb060_alpha_dummy_061 x y))
              (Class.cv (nb060_alpha_dummy_062 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)),
          ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)),
          ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)),
          ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
          ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
          ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
          ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)),
          ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
          ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
          ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
          ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
          ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
          ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0008 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
        ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
        ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)),
        ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
        ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
        ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
        ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
        ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_051))
          (Class.cv (nb060_alpha_dummy_044))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_052))
            (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))
              (syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))
              (Class.cv (nb060_alpha_dummy_051))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y))
          (Class.cv (nb060_alpha_dummy_046 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_054 x y))
            (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))
              (syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))
              (Class.cv (nb060_alpha_dummy_053 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0078) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0079 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0076) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0077 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_044))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_046 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0052) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0053 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0052) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0053 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb060_alpha_dummy_059), (nb060_alpha_dummy_062 x y)),
                                  ((nb060_alpha_dummy_058), (nb060_alpha_dummy_061 x y)),
                                  ((nb060_alpha_dummy_057), (nb060_alpha_dummy_060 x y)),
                                  ((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
                                  ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
                                  ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
                                  ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)),
                                  ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
                                  ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                                  ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                                  ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
                                  ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                                  ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                                  ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                                  ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                    (nb060_alpha_dummy_006 x y z r a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb060_split_alpha_0007 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
                      ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
                      ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
                      ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)),
                      ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
                      ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                      ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                      ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
                      ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                      ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                      ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                      ((nb060_alpha_dummy_001), r),
                      ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb060_alpha_dummy_055), (nb060_alpha_dummy_056 x y)),
                      ((nb060_alpha_dummy_051), (nb060_alpha_dummy_053 x y)),
                      ((nb060_alpha_dummy_052), (nb060_alpha_dummy_054 x y)),
                      ((nb060_alpha_dummy_077), (nb060_alpha_dummy_078 x y)),
                      ((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
                      ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                      ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                      ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
                      ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                      ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                      ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                      ((nb060_alpha_dummy_001), r),
                      ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb060_split_alpha_0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
        ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_073))
          (Class.cab (nb060_alpha_dummy_043)
            (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb060_alpha_dummy_073))
            (Class.cab (nb060_alpha_dummy_043)
              (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_043))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_074 x y))
          (Class.cab (nb060_alpha_dummy_045 x y)
            (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb060_alpha_dummy_074 x y))
            (Class.cab (nb060_alpha_dummy_045 x y)
              (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0074) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0075 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0071) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0073 x y) 0))
                        (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_002))).fv ∪
                      ((Class.cv (nb060_alpha_dummy_003))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb060_split_alpha_0008 x y z r a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                    (nb060_split_alpha_0008 x y z r a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
                          ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                          ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                          ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
                          ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                          ((nb060_alpha_dummy_001), r),
                          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0074) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0075 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0071) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb060_alpha_dummy_002))).fv ∪
                        ((Class.cv (nb060_alpha_dummy_003))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb060_split_alpha_0008 x y z r a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb060_split_alpha_0008 x y z r a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb060_alpha_dummy_075), (nb060_alpha_dummy_076 x y)),
                            ((nb060_alpha_dummy_044), (nb060_alpha_dummy_046 x y)),
                            ((nb060_alpha_dummy_043), (nb060_alpha_dummy_045 x y)),
                            ((nb060_alpha_dummy_073), (nb060_alpha_dummy_074 x y)),
                            ((nb060_alpha_dummy_047), (nb060_alpha_dummy_048 x y)),
                            ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                            ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                            ((nb060_alpha_dummy_001), r),
                            ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0010 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)),
        ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)),
        ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)),
        ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
        ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
        ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
        ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
        ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
        ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)),
        ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_093))
            (syn_cun (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_096 y z))
            (syn_cun (Class.cv (nb060_alpha_dummy_097 y z))
              (Class.cv (nb060_alpha_dummy_098 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)),
          ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)),
          ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)),
          ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
          ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
          ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
          ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
          ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
          ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)),
          ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
          ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part008`. -/


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
noncomputable def nb060_split_alpha_0011 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
        ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
        ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)),
        ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_080))
          (Class.cv (nb060_alpha_dummy_003))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
            (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_082 y z)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
            (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0084) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0085 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0081) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0083 y z) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_003))).fv ∪
                ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide))
            (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_080))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060_alpha_dummy_082 y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0090) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0091 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0090) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0091 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_095),
        (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)),
        ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091),
        (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
        ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080),
        (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
        ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083),
        (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z),
        ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060_split_alpha_0010 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
                              ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
                              ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
                              ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                              ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                              ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)),
                              ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
                              ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
                              ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
                              ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                              ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                              ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)),
                              ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0012 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)),
        ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)),
        ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)),
        ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
        ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
        ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
        ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)),
        ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
        ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
        ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
        ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
        ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_093))
            (syn_cun (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_097 y z))
            (Class.cv (nb060_alpha_dummy_098 y z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_096 y z))
            (syn_cun (Class.cv (nb060_alpha_dummy_097 y z))
              (Class.cv (nb060_alpha_dummy_098 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)),
          ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)),
          ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)),
          ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
          ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
          ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
          ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)),
          ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
          ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
          ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
          ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
          ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
          ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0013 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
        ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
        ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)),
        ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
        ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
        ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
        ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
        ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_087))
          (Class.cv (nb060_alpha_dummy_080))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_088))
            (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))
              (syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))
              (Class.cv (nb060_alpha_dummy_087))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z))
          (Class.cv (nb060_alpha_dummy_082 y z))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_090 y z))
            (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))
              (syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))
              (Class.cv (nb060_alpha_dummy_089 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0116) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0117 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0114) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0115 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_080))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_082 y z))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0090) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0091 y z) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0090) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0091 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)),
                                  ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)),
                                  ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)),
                                  ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
                                  ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
                                  ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
                                  ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)),
                                  ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
                                  ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                                  ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                                  ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
                                  ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                                  ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                                  ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                                  ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                    (nb060_alpha_dummy_006 x y z r a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb060_split_alpha_0012 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
                      ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
                      ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
                      ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)),
                      ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
                      ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                      ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                      ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
                      ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                      ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                      ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                      ((nb060_alpha_dummy_001), r),
                      ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)),
                      ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)),
                      ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)),
                      ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)),
                      ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
                      ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                      ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                      ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
                      ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                      ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                      ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                      ((nb060_alpha_dummy_001), r),
                      ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb060_split_alpha_0014 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaClass
      [((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Class.cab (nb060_alpha_dummy_109) (syn_wnan
          (Wff.classMem (Class.cv (nb060_alpha_dummy_109)) (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                    (syn_csn (syn_c0c))))))) (Wff.classMem (Class.cv (nb060_alpha_dummy_109))
            (Class.cab (nb060_alpha_dummy_079)
              (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_079))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080)))
                    (syn_csn (syn_c0c)))))))))
      (Class.cab (nb060_alpha_dummy_110 y z) (syn_wnan
          (Wff.classMem (Class.cv (nb060_alpha_dummy_110 y z))
            (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                    (syn_csn (syn_c0c)))))))
          (Wff.classMem (Class.cv (nb060_alpha_dummy_110 y z))
            (Class.cab (nb060_alpha_dummy_081 y z)
              (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0112) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0113 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0109) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0111 y z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060_alpha_dummy_003))).fv ∪
                          ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide))
                      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0013 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0013 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
                              ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                              ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                              ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
                              ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_ccompl (syn_csn (syn_c0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0112) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0113 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0109) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0111 y z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060_alpha_dummy_003))).fv ∪
                          ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide))
                      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0013 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0013 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)),
                              ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)),
                              ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)),
                              ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)),
                              ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_ccompl (syn_csn (syn_c0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn,
                                fv_syn_c0c]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part009`. -/


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
noncomputable def nb060_split_alpha_0015 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_131), (nb060_alpha_dummy_134 x z)),
        ((nb060_alpha_dummy_130), (nb060_alpha_dummy_133 x z)),
        ((nb060_alpha_dummy_129), (nb060_alpha_dummy_132 x z)),
        ((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
        ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
        ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
        ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
        ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
        ((nb060_alpha_dummy_121), (nb060_alpha_dummy_122 x z)),
        ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_129))
            (syn_cun (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_132 x z))
            (syn_cun (Class.cv (nb060_alpha_dummy_133 x z))
              (Class.cv (nb060_alpha_dummy_134 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_131), (nb060_alpha_dummy_134 x z)),
          ((nb060_alpha_dummy_130), (nb060_alpha_dummy_133 x z)),
          ((nb060_alpha_dummy_129), (nb060_alpha_dummy_132 x z)),
          ((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
          ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
          ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
          ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
          ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
          ((nb060_alpha_dummy_121), (nb060_alpha_dummy_122 x z)),
          ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
          ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0016 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    TAlphaWff
      [((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
        ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
        ((nb060_alpha_dummy_121), (nb060_alpha_dummy_122 x z)),
        ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_116))
          (Class.cv (nb060_alpha_dummy_002))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
            (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_118 x z)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
            (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0122) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0123 x z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0119) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0121 x z) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_002))).fv ∪
                ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_116))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060_alpha_dummy_118 x z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0128) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0129 x z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0128) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0129 x z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0126) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0127 x z) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb060_alpha_dummy_131),
        (nb060_alpha_dummy_134 x z)), ((nb060_alpha_dummy_130), (nb060_alpha_dummy_133 x z)),
        ((nb060_alpha_dummy_129), (nb060_alpha_dummy_132 x z)), ((nb060_alpha_dummy_127),
        (nb060_alpha_dummy_128 x z)), ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
        ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)), ((nb060_alpha_dummy_116),
        (nb060_alpha_dummy_118 x z)), ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
        ((nb060_alpha_dummy_121), (nb060_alpha_dummy_122 x z)), ((nb060_alpha_dummy_119),
        (nb060_alpha_dummy_120 x z)), ((nb060_alpha_dummy_004), z),
        ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x),
        ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
        (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060_split_alpha_0015 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
                              ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
                              ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
                              ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                              ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                              ((nb060_alpha_dummy_121), (nb060_alpha_dummy_122 x z)),
                              ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
                              ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
                              ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
                              ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                              ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                              ((nb060_alpha_dummy_121), (nb060_alpha_dummy_122 x z)),
                              ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb060_split_alpha_0017 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_131), (nb060_alpha_dummy_134 x z)),
        ((nb060_alpha_dummy_130), (nb060_alpha_dummy_133 x z)),
        ((nb060_alpha_dummy_129), (nb060_alpha_dummy_132 x z)),
        ((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
        ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
        ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
        ((nb060_alpha_dummy_149), (nb060_alpha_dummy_150 x z)),
        ((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
        ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
        ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
        ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
        ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_129))
            (syn_cun (Class.cv (nb060_alpha_dummy_130)) (Class.cv (nb060_alpha_dummy_131))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_133 x z))
            (Class.cv (nb060_alpha_dummy_134 x z))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_132 x z))
            (syn_cun (Class.cv (nb060_alpha_dummy_133 x z))
              (Class.cv (nb060_alpha_dummy_134 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb060_alpha_dummy_131), (nb060_alpha_dummy_134 x z)),
          ((nb060_alpha_dummy_130), (nb060_alpha_dummy_133 x z)),
          ((nb060_alpha_dummy_129), (nb060_alpha_dummy_132 x z)),
          ((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
          ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
          ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
          ((nb060_alpha_dummy_149), (nb060_alpha_dummy_150 x z)),
          ((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
          ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
          ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
          ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
          ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
          ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
          ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
          ((nb060_alpha_dummy_001), r),
          ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part010`. -/


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
noncomputable def nb060_split_alpha_0018 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
        ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
        ((nb060_alpha_dummy_149), (nb060_alpha_dummy_150 x z)),
        ((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
        ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
        ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
        ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
        ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_123))
          (Class.cv (nb060_alpha_dummy_116))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_124))
            (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))
              (syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))
              (Class.cv (nb060_alpha_dummy_123))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z))
          (Class.cv (nb060_alpha_dummy_118 x z))) (Wff.neg
          (Wff.classEq (Class.cv (nb060_alpha_dummy_126 x z))
            (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))
              (syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))
              (Class.cv (nb060_alpha_dummy_125 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0154) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0155 x z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0152) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0153 x z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_116))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb060_alpha_dummy_118 x z))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0128) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0129 x z) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0128) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0129 x z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0126) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb060_alpha_dummy_131), (nb060_alpha_dummy_134 x z)),
                                  ((nb060_alpha_dummy_130), (nb060_alpha_dummy_133 x z)),
                                  ((nb060_alpha_dummy_129), (nb060_alpha_dummy_132 x z)),
                                  ((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
                                  ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
                                  ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
                                  ((nb060_alpha_dummy_149), (nb060_alpha_dummy_150 x z)),
                                  ((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
                                  ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                                  ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                                  ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
                                  ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                                  ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                                  ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                                  ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                    (nb060_alpha_dummy_006 x y z r a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb060_split_alpha_0017 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
                      ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
                      ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
                      ((nb060_alpha_dummy_149), (nb060_alpha_dummy_150 x z)),
                      ((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
                      ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                      ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                      ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
                      ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                      ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                      ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                      ((nb060_alpha_dummy_001), r),
                      ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb060_alpha_dummy_127), (nb060_alpha_dummy_128 x z)),
                      ((nb060_alpha_dummy_123), (nb060_alpha_dummy_125 x z)),
                      ((nb060_alpha_dummy_124), (nb060_alpha_dummy_126 x z)),
                      ((nb060_alpha_dummy_149), (nb060_alpha_dummy_150 x z)),
                      ((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
                      ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                      ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                      ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
                      ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                      ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                      ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                      ((nb060_alpha_dummy_001), r),
                      ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb060_split_alpha_0019 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaClass
      [((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
        ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
        ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
        ((nb060_alpha_dummy_001), r),
        ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))]
      (Class.cab (nb060_alpha_dummy_145) (syn_wnan
          (Wff.classMem (Class.cv (nb060_alpha_dummy_145)) (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                    (syn_csn (syn_c0c))))))) (Wff.classMem (Class.cv (nb060_alpha_dummy_145))
            (Class.cab (nb060_alpha_dummy_115)
              (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb060_alpha_dummy_115))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116)))
                    (syn_csn (syn_c0c)))))))))
      (Class.cab (nb060_alpha_dummy_146 x z) (syn_wnan
          (Wff.classMem (Class.cv (nb060_alpha_dummy_146 x z))
            (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                    (syn_csn (syn_c0c)))))))
          (Wff.classMem (Class.cv (nb060_alpha_dummy_146 x z))
            (Class.cab (nb060_alpha_dummy_117 x z)
              (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z))
                  (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0150) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0151 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0147) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0149 x z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060_alpha_dummy_002))).fv ∪
                          ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide))
                      (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0018 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0018 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
                              ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                              ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                              ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
                              ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_ccompl (syn_csn (syn_c0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0150) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0151 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0147) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0149 x z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060_alpha_dummy_002))).fv ∪
                          ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide))
                      (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0018 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060_split_alpha_0018 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb060_alpha_dummy_147), (nb060_alpha_dummy_148 x z)),
                              ((nb060_alpha_dummy_116), (nb060_alpha_dummy_118 x z)),
                              ((nb060_alpha_dummy_115), (nb060_alpha_dummy_117 x z)),
                              ((nb060_alpha_dummy_145), (nb060_alpha_dummy_146 x z)),
                              ((nb060_alpha_dummy_119), (nb060_alpha_dummy_120 x z)),
                              ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y),
                              ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a),
                              ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005),
                                (nb060_alpha_dummy_006 x y z r a))]
                            (syn_ccompl (syn_csn (syn_c0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn,
                                fv_syn_c0c]))))))))))))))

@[expose]
noncomputable def nominal_df_trans (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_a_z : a ≠ z) (dv_r_x : r ≠ x)
    (dv_r_y : r ≠ y) (dv_r_z : r ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_ctrans) (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a)
              (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y))
                    (syn_wbr (.cv y) (.cv r) (.cv z)))
                  (syn_wbr (.cv x) (.cv r) (.cv z)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb060_split_alpha_0004 x y z r a dv_a_r) (TAlphaWff.all
                (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_x
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.all (TAlphaWff.imp
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_z
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_y
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_a_x (TAlphaVar.here _ _ _)))))) (TAlphaWff.imp
                            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060_split_alpha_0006 x y z r a dv_x_y dv_x_z))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060_split_alpha_0006 x y z r a dv_x_y dv_x_z))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0009 x y z r a dv_y_z))))))))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_r_x (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (Ne.symm dv_a_r) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060_split_alpha_0011 x y z r a dv_y_z))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060_split_alpha_0011 x y z r a dv_y_z))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb060_split_alpha_0014 x y z r a))))) (TAlphaClass.cv
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_r_x (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060_split_alpha_0016 x y z r a dv_x_y dv_x_z))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060_split_alpha_0016 x y z r a dv_x_y dv_x_z))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (nb060_split_alpha_0019 x y z r a))))) (TAlphaClass.cv
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) (Ne.symm dv_a_r) (TAlphaVar.here _ _ _))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
