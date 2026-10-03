/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C056C001Part005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C056C001Part006`. -/


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
noncomputable def nb056_split_alpha_0000 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)),
        ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)),
        ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)),
        ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
        ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
        ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
        ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
        ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
        ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)),
        ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_027))
            (syn_cun (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_030 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_031 f))
              (Class.cv (nb056_alpha_dummy_032 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)),
          ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)),
          ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)),
          ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
          ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
          ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
          ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
          ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
          ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)),
          ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0001 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
        ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
        ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)),
        ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
        (syn_cphi (Class.cv (nb056_alpha_dummy_014))))
      (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
        (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
            ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb056_alpha_dummy_014))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb056_alpha_dummy_016 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0014) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0015 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0014) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0015 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0012) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)),
                                      ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)),
                                      ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)),
                                      ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
                                      ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
                                      ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
                                      ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                                      ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                                      ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)),
                                      ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                      ((nb056_alpha_dummy_000), f)]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb056_split_alpha_0000 f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
                          ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
                          ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
                          ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                          ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                          ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)),
                          ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
                          ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
                          ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
                          ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                          ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                          ((nb056_alpha_dummy_019), (nb056_alpha_dummy_020 f)),
                          ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0002 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)),
        ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)),
        ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)),
        ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
        ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
        ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
        ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)),
        ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
        ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
        ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
        ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
        ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_027))
            (syn_cun (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_030 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_031 f))
              (Class.cv (nb056_alpha_dummy_032 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)),
          ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)),
          ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)),
          ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
          ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
          ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
          ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)),
          ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
          ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
          ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
          ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
          ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part007`. -/


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
noncomputable def nb056_split_alpha_0003 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
        ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
        ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)),
        ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
        ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
        ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
        ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
        ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_021))
          (Class.cv (nb056_alpha_dummy_014))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_022))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_021))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_023 f))
          (Class.cv (nb056_alpha_dummy_016 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_024 f))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_023 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0040) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0041 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0038) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0039 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_014))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_016 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0014) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0015 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0014) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0015 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb056_alpha_dummy_029), (nb056_alpha_dummy_032 f)),
                                  ((nb056_alpha_dummy_028), (nb056_alpha_dummy_031 f)),
                                  ((nb056_alpha_dummy_027), (nb056_alpha_dummy_030 f)),
                                  ((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
                                  ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
                                  ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
                                  ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)),
                                  ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
                                  ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                                  ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                                  ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
                                  ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                  ((nb056_alpha_dummy_000), f)]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056_split_alpha_0002 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
                      ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
                      ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
                      ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)),
                      ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
                      ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                      ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                      ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
                      ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_025), (nb056_alpha_dummy_026 f)),
                      ((nb056_alpha_dummy_021), (nb056_alpha_dummy_023 f)),
                      ((nb056_alpha_dummy_022), (nb056_alpha_dummy_024 f)),
                      ((nb056_alpha_dummy_047), (nb056_alpha_dummy_048 f)),
                      ((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
                      ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                      ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                      ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
                      ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb056_split_alpha_0004 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
        ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_043))
          (Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_043))
            (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_044 f))
          (Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056_alpha_dummy_044 f))
            (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0036) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0037 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0033) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0035 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0003 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0003 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
                          ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                          ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                          ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
                          ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0036) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0037 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0033) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0035 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056_alpha_dummy_005))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_006))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0003 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0003 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb056_alpha_dummy_045), (nb056_alpha_dummy_046 f)),
                            ((nb056_alpha_dummy_014), (nb056_alpha_dummy_016 f)),
                            ((nb056_alpha_dummy_013), (nb056_alpha_dummy_015 f)),
                            ((nb056_alpha_dummy_043), (nb056_alpha_dummy_044 f)),
                            ((nb056_alpha_dummy_017), (nb056_alpha_dummy_018 f)),
                            ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                            ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                            ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                            ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                            ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                            ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0005 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)),
        ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)),
        ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)),
        ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
        ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
        ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
        ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
        ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
        ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)),
        ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_063))
            (syn_cun (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_066 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_067 f))
              (Class.cv (nb056_alpha_dummy_068 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)),
          ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)),
          ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)),
          ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
          ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
          ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
          ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
          ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
          ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)),
          ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0006 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
        ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
        ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)),
        ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
        (syn_cphi (Class.cv (nb056_alpha_dummy_050))))
      (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
        (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
            ((Class.cv (nb056_alpha_dummy_010 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb056_alpha_dummy_050))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb056_alpha_dummy_052 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0052) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0053 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0052) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0053 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0050) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)),
                                      ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)),
                                      ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)),
                                      ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
                                      ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
                                      ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
                                      ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                                      ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                                      ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)),
                                      ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                      ((nb056_alpha_dummy_000), f)]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb056_split_alpha_0005 f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
                          ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
                          ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
                          ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                          ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                          ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)),
                          ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
                          ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
                          ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
                          ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                          ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                          ((nb056_alpha_dummy_055), (nb056_alpha_dummy_056 f)),
                          ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part008`. -/


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
noncomputable def nb056_split_alpha_0007 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)),
        ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)),
        ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)),
        ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
        ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
        ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
        ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)),
        ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
        ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
        ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
        ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
        ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_063))
            (syn_cun (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_066 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_067 f))
              (Class.cv (nb056_alpha_dummy_068 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)),
          ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)),
          ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)),
          ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
          ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
          ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
          ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)),
          ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
          ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
          ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
          ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
          ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0008 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
        ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
        ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)),
        ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
        ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
        ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
        ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
        ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_057))
          (Class.cv (nb056_alpha_dummy_050))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_058))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_057))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_059 f))
          (Class.cv (nb056_alpha_dummy_052 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_060 f))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_059 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0078) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0079 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0076) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0077 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_050))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_052 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0052) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0053 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0052) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0053 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb056_alpha_dummy_065), (nb056_alpha_dummy_068 f)),
                                  ((nb056_alpha_dummy_064), (nb056_alpha_dummy_067 f)),
                                  ((nb056_alpha_dummy_063), (nb056_alpha_dummy_066 f)),
                                  ((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
                                  ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
                                  ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
                                  ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)),
                                  ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
                                  ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                                  ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                                  ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
                                  ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                  ((nb056_alpha_dummy_000), f)]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056_split_alpha_0007 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
                      ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
                      ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
                      ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)),
                      ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
                      ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                      ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                      ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
                      ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_061), (nb056_alpha_dummy_062 f)),
                      ((nb056_alpha_dummy_057), (nb056_alpha_dummy_059 f)),
                      ((nb056_alpha_dummy_058), (nb056_alpha_dummy_060 f)),
                      ((nb056_alpha_dummy_083), (nb056_alpha_dummy_084 f)),
                      ((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
                      ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                      ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                      ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
                      ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb056_split_alpha_0009 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
        ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_079))
          (Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_079))
            (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_080 f))
          (Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056_alpha_dummy_080 f))
            (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0074) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0075 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0071) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0073 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_005))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_007))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_010 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0008 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0008 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
                          ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                          ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                          ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
                          ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0074) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0075 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0071) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0073 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056_alpha_dummy_005))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_007))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_010 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0008 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0008 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb056_alpha_dummy_081), (nb056_alpha_dummy_082 f)),
                            ((nb056_alpha_dummy_050), (nb056_alpha_dummy_052 f)),
                            ((nb056_alpha_dummy_049), (nb056_alpha_dummy_051 f)),
                            ((nb056_alpha_dummy_079), (nb056_alpha_dummy_080 f)),
                            ((nb056_alpha_dummy_053), (nb056_alpha_dummy_054 f)),
                            ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                            ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                            ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                            ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                            ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                            ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                            ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part009`. -/


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
noncomputable def nb056_split_alpha_0010 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)),
        ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)),
        ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)),
        ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
        ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
        ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
        ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
        ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
        ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)),
        ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_105))
            (syn_cun (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_108 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_109 f))
              (Class.cv (nb056_alpha_dummy_110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)),
          ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)),
          ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)),
          ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
          ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
          ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
          ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
          ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
          ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)),
          ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
          ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
          ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
          ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0011 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
        ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
        ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
        ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
        ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)),
        ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_099))
          (Class.cv (nb056_alpha_dummy_092))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_100))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_101 f))
          (Class.cv (nb056_alpha_dummy_094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_102 f))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0094) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0095 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)),
                                  ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)),
                                  ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)),
                                  ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
                                  ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
                                  ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
                                  ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                                  ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                                  ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)),
                                  ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                                  ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                                  ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                                  ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                  ((nb056_alpha_dummy_000), f)]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056_split_alpha_0010 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
                      ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
                      ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
                      ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                      ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                      ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)),
                      ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                      ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                      ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                      ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
                      ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
                      ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
                      ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                      ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                      ((nb056_alpha_dummy_097), (nb056_alpha_dummy_098 f)),
                      ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                      ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                      ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                      ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb056_split_alpha_0012 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)),
        ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)),
        ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)),
        ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
        ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
        ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
        ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)),
        ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
        ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
        ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
        ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
        ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_105))
            (syn_cun (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_108 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_109 f))
              (Class.cv (nb056_alpha_dummy_110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)),
          ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)),
          ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)),
          ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
          ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
          ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
          ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)),
          ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
          ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
          ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
          ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
          ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
          ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
          ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
          ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part010`. -/


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
noncomputable def nb056_split_alpha_0013 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
        ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
        ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)),
        ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
        ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
        ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
        ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
        ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.classEq (Class.cv (nb056_alpha_dummy_100))
        (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))
          (syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))
          (Class.cv (nb056_alpha_dummy_099))))
      (Wff.classEq (Class.cv (nb056_alpha_dummy_102 f))
        (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))
          (Class.cv (nb056_alpha_dummy_101 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb056_alpha_dummy_092))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb056_alpha_dummy_094 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 1))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 1))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb056_alpha_dummy_107), (nb056_alpha_dummy_110 f)),
                              ((nb056_alpha_dummy_106), (nb056_alpha_dummy_109 f)),
                              ((nb056_alpha_dummy_105), (nb056_alpha_dummy_108 f)),
                              ((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
                              ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
                              ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
                              ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)),
                              ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
                              ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                              ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                              ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
                              ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                              ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                              ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                              ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                              ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                              ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                              ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                              ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                              ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                              ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                              ((nb056_alpha_dummy_000), f)]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb056_split_alpha_0012 f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
                  ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
                  ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
                  ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)),
                  ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
                  ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                  ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                  ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
                  ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                  ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                  ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                  ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                  ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb056_alpha_dummy_103), (nb056_alpha_dummy_104 f)),
                  ((nb056_alpha_dummy_099), (nb056_alpha_dummy_101 f)),
                  ((nb056_alpha_dummy_100), (nb056_alpha_dummy_102 f)),
                  ((nb056_alpha_dummy_125), (nb056_alpha_dummy_126 f)),
                  ((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
                  ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                  ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                  ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
                  ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                  ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                  ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                  ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                  ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb056_split_alpha_0014 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
        ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_121))
          (Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_121))
            (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_122 f))
          (Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056_alpha_dummy_122 f))
            (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0116) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0117 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0113) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0115 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0090) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _)))))))
                                    (nb056_split_alpha_0013 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0090) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _)))))))
                                    (nb056_split_alpha_0013 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
                          ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                          ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                          ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
                          ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                          ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                          ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                          ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0116) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0117 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0113) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0115 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056_alpha_dummy_085))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _)))))))
                                      (nb056_split_alpha_0013 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0091 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0120) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0121 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0118) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0119 f) 0)) (TAlphaVar.here _ _ _)))))))
                                      (nb056_split_alpha_0013 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb056_alpha_dummy_123), (nb056_alpha_dummy_124 f)),
                            ((nb056_alpha_dummy_092), (nb056_alpha_dummy_094 f)),
                            ((nb056_alpha_dummy_091), (nb056_alpha_dummy_093 f)),
                            ((nb056_alpha_dummy_121), (nb056_alpha_dummy_122 f)),
                            ((nb056_alpha_dummy_095), (nb056_alpha_dummy_096 f)),
                            ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                            ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                            ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                            ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                            ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                            ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                            ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                            ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                            ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                            ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0015 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)),
        ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)),
        ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)),
        ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
        ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
        ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
        ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
        ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
        ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)),
        ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_141))
            (syn_cun (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_144 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_145 f))
              (Class.cv (nb056_alpha_dummy_146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)),
          ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)),
          ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)),
          ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
          ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
          ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
          ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
          ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
          ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)),
          ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
          ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
          ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
          ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part011`. -/


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
noncomputable def nb056_split_alpha_0016 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
        ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
        ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
        ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
        ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)),
        ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_135))
          (Class.cv (nb056_alpha_dummy_128))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_136))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_135))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_137 f))
          (Class.cv (nb056_alpha_dummy_130 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_138 f))
            (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))
              (Class.cv (nb056_alpha_dummy_137 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0132) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0133 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0132) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0133 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0130) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed
                                [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)),
                                  ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)),
                                  ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)),
                                  ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
                                  ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
                                  ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
                                  ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                                  ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                                  ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)),
                                  ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                                  ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                                  ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                                  ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                  ((nb056_alpha_dummy_000), f)]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056_split_alpha_0015 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
                      ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
                      ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
                      ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                      ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                      ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)),
                      ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                      ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                      ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                      ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
                      ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
                      ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
                      ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                      ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                      ((nb056_alpha_dummy_133), (nb056_alpha_dummy_134 f)),
                      ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                      ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                      ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                      ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                      ((nb056_alpha_dummy_000), f)]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb056_split_alpha_0017 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)),
        ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)),
        ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)),
        ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
        ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
        ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
        ((nb056_alpha_dummy_161), (nb056_alpha_dummy_162 f)),
        ((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
        ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
        ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
        ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
        ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_141))
            (syn_cun (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_144 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_145 f))
              (Class.cv (nb056_alpha_dummy_146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)),
          ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)),
          ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)),
          ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
          ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
          ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
          ((nb056_alpha_dummy_161), (nb056_alpha_dummy_162 f)),
          ((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
          ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
          ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
          ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
          ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
          ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
          ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
          ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0018 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
        ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
        ((nb056_alpha_dummy_161), (nb056_alpha_dummy_162 f)),
        ((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
        ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
        ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
        ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
        ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.classEq (Class.cv (nb056_alpha_dummy_136))
        (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))
          (syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))
          (Class.cv (nb056_alpha_dummy_135))))
      (Wff.classEq (Class.cv (nb056_alpha_dummy_138 f))
        (syn_cif (Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))
          (syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))
          (Class.cv (nb056_alpha_dummy_137 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb056_alpha_dummy_128))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb056_alpha_dummy_130 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0132) 1))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0133 f) 1))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0132) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0133 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_closed
                            [((nb056_alpha_dummy_143), (nb056_alpha_dummy_146 f)),
                              ((nb056_alpha_dummy_142), (nb056_alpha_dummy_145 f)),
                              ((nb056_alpha_dummy_141), (nb056_alpha_dummy_144 f)),
                              ((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
                              ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
                              ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
                              ((nb056_alpha_dummy_161), (nb056_alpha_dummy_162 f)),
                              ((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
                              ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                              ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                              ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
                              ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                              ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                              ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                              ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                              ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                              ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                              ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                              ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                              ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                              ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                              ((nb056_alpha_dummy_000), f)]
                            (syn_c1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb056_split_alpha_0017 f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
                  ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
                  ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
                  ((nb056_alpha_dummy_161), (nb056_alpha_dummy_162 f)),
                  ((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
                  ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                  ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                  ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
                  ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                  ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                  ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                  ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                  ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                [((nb056_alpha_dummy_139), (nb056_alpha_dummy_140 f)),
                  ((nb056_alpha_dummy_135), (nb056_alpha_dummy_137 f)),
                  ((nb056_alpha_dummy_136), (nb056_alpha_dummy_138 f)),
                  ((nb056_alpha_dummy_161), (nb056_alpha_dummy_162 f)),
                  ((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
                  ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                  ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                  ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
                  ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                  ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                  ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                  ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                  ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                  ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                  ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                  ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                  ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                  ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                  ((nb056_alpha_dummy_000), f)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))

@[expose]
noncomputable def nb056_split_alpha_0019 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
        ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
        ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_157))
          (Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056_alpha_dummy_157))
            (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056_alpha_dummy_158 f))
          (Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056_alpha_dummy_158 f))
            (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0154) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0155 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0151) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0153 f) 0))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056_alpha_dummy_086))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_085))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
                      ((Class.cv (nb056_alpha_dummy_087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0128) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0129 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0128) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0129 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _)))))))
                                    (nb056_split_alpha_0018 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0128) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0129 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0128) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0129 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _)))))))
                                    (nb056_split_alpha_0018 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
                          ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                          ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                          ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
                          ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                          ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                          ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                          ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0154) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0155 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0151) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056_alpha_dummy_086))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_085))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
                        ((Class.cv (nb056_alpha_dummy_087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0129 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _)))))))
                                      (nb056_split_alpha_0018 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 0))
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 0)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 1)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0129 f) 1)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0158) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0159 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0156) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0157 f) 0)) (TAlphaVar.here _ _ _)))))))
                                      (nb056_split_alpha_0018 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb056_alpha_dummy_159), (nb056_alpha_dummy_160 f)),
                            ((nb056_alpha_dummy_128), (nb056_alpha_dummy_130 f)),
                            ((nb056_alpha_dummy_127), (nb056_alpha_dummy_129 f)),
                            ((nb056_alpha_dummy_157), (nb056_alpha_dummy_158 f)),
                            ((nb056_alpha_dummy_131), (nb056_alpha_dummy_132 f)),
                            ((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
                            ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
                            ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
                            ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                            ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                            ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                            ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                            ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                            ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                            ((nb056_alpha_dummy_000), f)] (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part012`. -/


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
noncomputable def nb056_variable_occurrence (f : Var) :
    TAlphaClass
      [(nb056_alpha_dummy_086, (nb056_alpha_dummy_088 f)),
        (nb056_alpha_dummy_085, (nb056_alpha_dummy_087 f)),
        (nb056_alpha_dummy_089, (nb056_alpha_dummy_090 f)),
        (nb056_alpha_dummy_007, (nb056_alpha_dummy_010 f)),
        (nb056_alpha_dummy_006, (nb056_alpha_dummy_009 f)),
        (nb056_alpha_dummy_005, (nb056_alpha_dummy_008 f)),
        (nb056_alpha_dummy_011, (nb056_alpha_dummy_012 f)),
        (nb056_alpha_dummy_003, (nb056_alpha_dummy_004 f)),
        (nb056_alpha_dummy_001, (nb056_alpha_dummy_002 f)), (nb056_alpha_dummy_000, f)]
      (Class.cv nb056_alpha_dummy_000) (Class.cv f) :=
  by
  have freshness0 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_086 :=
    by
    unfold nb056_alpha_dummy_086
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0170) 1))
  have freshness1 : f ≠ (nb056_alpha_dummy_088 f) :=
    by
    unfold nb056_alpha_dummy_088
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0171 f) 1))
  have freshness2 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_085 :=
    by
    unfold nb056_alpha_dummy_085
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0170) 0))
  have freshness3 : f ≠ (nb056_alpha_dummy_087 f) :=
    by
    unfold nb056_alpha_dummy_087
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0171 f) 0))
  have freshness4 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_089 :=
    by
    unfold nb056_alpha_dummy_089
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0168) 0))
  have freshness5 : f ≠ (nb056_alpha_dummy_090 f) :=
    by
    unfold nb056_alpha_dummy_090
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0169 f) 0))
  have freshness6 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_007 :=
    by
    unfold nb056_alpha_dummy_007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  have freshness7 : f ≠ (nb056_alpha_dummy_010 f) :=
    by
    unfold nb056_alpha_dummy_010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  have freshness8 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_006 :=
    by
    unfold nb056_alpha_dummy_006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 1))
  have freshness9 : f ≠ (nb056_alpha_dummy_009 f) :=
    by
    unfold nb056_alpha_dummy_009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 1))
  have freshness10 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_005 :=
    by
    unfold nb056_alpha_dummy_005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 0))
  have freshness11 : f ≠ (nb056_alpha_dummy_008 f) :=
    by
    unfold nb056_alpha_dummy_008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 0))
  have freshness12 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_011 :=
    by
    unfold nb056_alpha_dummy_011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0165) 0))
  have freshness13 : f ≠ (nb056_alpha_dummy_012 f) :=
    by
    unfold nb056_alpha_dummy_012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0167 f) 0))
  have freshness14 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_003 :=
    by
    unfold nb056_alpha_dummy_003
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0162) 0))
  have freshness15 : f ≠ (nb056_alpha_dummy_004 f) :=
    by
    unfold nb056_alpha_dummy_004
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0163 f) 0))
  have freshness16 : nb056_alpha_dummy_000 ≠ nb056_alpha_dummy_001 :=
    by
    unfold nb056_alpha_dummy_001
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0160) 0))
  have freshness17 : f ≠ (nb056_alpha_dummy_002 f) :=
    by
    unfold nb056_alpha_dummy_002
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0161 f) 0))
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
noncomputable def nb056_split_alpha_0020 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_086), (nb056_alpha_dummy_088 f)),
        ((nb056_alpha_dummy_085), (nb056_alpha_dummy_087 f)),
        ((nb056_alpha_dummy_089), (nb056_alpha_dummy_090 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq (Class.cv (nb056_alpha_dummy_089))
          (syn_cop (Class.cv (nb056_alpha_dummy_085)) (Class.cv (nb056_alpha_dummy_086))))
        (Wff.neg (syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_085)))))
      (Wff.imp (Wff.classEq (Class.cv (nb056_alpha_dummy_090 f))
          (syn_cop (Class.cv (nb056_alpha_dummy_087 f)) (Class.cv (nb056_alpha_dummy_088 f))))
        (Wff.neg (syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_087 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0082) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0083 f) 0)))
          (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0080) 0)))
            (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0081 f) 0)))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb056_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪
                                      ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
                                      ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0011 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb056_alpha_dummy_000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb056_alpha_dummy_085))).fv ∪
                                      ((Class.cv (nb056_alpha_dummy_086))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
                                      ((Class.cv (nb056_alpha_dummy_088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056_split_alpha_0011 f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0014 f))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0122) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0122) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0126) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0127 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0123) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0125 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb056_alpha_dummy_086))).fv ∪
                                        ((Class.cv (nb056_alpha_dummy_085))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
                                        ((Class.cv (nb056_alpha_dummy_087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0016 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0122) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0122) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0126) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0127 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0123) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0125 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb056_alpha_dummy_086))).fv ∪
                                        ((Class.cv (nb056_alpha_dummy_085))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
                                        ((Class.cv (nb056_alpha_dummy_087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056_split_alpha_0016 f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb056_split_alpha_0019 f))))))))
        (nb056_variable_occurrence f))))

@[expose]
noncomputable def nb056_split_alpha_0021 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)),
        ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)),
        ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)),
        ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
        ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
        ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
        ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
        ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
        ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)),
        ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb056_alpha_dummy_177))
            (syn_cun (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056_alpha_dummy_180 f))
            (syn_cun (Class.cv (nb056_alpha_dummy_181 f))
              (Class.cv (nb056_alpha_dummy_182 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)),
          ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)),
          ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)),
          ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
          ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
          ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
          ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
          ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
          ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)),
          ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)), ((nb056_alpha_dummy_000), f)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb056_split_alpha_0022 (f : Var) :
    TAlphaWff
      [((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
        ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
        ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)),
        ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
        ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
        ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
        ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
        ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
        ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
        ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
        ((nb056_alpha_dummy_000), f)]
      (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
        (syn_cphi (Class.cv (nb056_alpha_dummy_164))))
      (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
        (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪
            ((Class.cv (nb056_alpha_dummy_009 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb056_alpha_dummy_164))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb056_alpha_dummy_166 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0182) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0183 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0182) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0183 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0180) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb056_alpha_dummy_179), (nb056_alpha_dummy_182 f)),
                                      ((nb056_alpha_dummy_178), (nb056_alpha_dummy_181 f)),
                                      ((nb056_alpha_dummy_177), (nb056_alpha_dummy_180 f)),
                                      ((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
                                      ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
                                      ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
                                      ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                                      ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                                      ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)),
                                      ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                                      ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                                      ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                                      ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                                      ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                                      ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                                      ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                                      ((nb056_alpha_dummy_000), f)]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb056_split_alpha_0021 f))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
                          ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
                          ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
                          ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                          ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                          ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)),
                          ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb056_alpha_dummy_175), (nb056_alpha_dummy_176 f)),
                          ((nb056_alpha_dummy_171), (nb056_alpha_dummy_173 f)),
                          ((nb056_alpha_dummy_172), (nb056_alpha_dummy_174 f)),
                          ((nb056_alpha_dummy_164), (nb056_alpha_dummy_166 f)),
                          ((nb056_alpha_dummy_163), (nb056_alpha_dummy_165 f)),
                          ((nb056_alpha_dummy_169), (nb056_alpha_dummy_170 f)),
                          ((nb056_alpha_dummy_167), (nb056_alpha_dummy_168 f)),
                          ((nb056_alpha_dummy_007), (nb056_alpha_dummy_010 f)),
                          ((nb056_alpha_dummy_006), (nb056_alpha_dummy_009 f)),
                          ((nb056_alpha_dummy_005), (nb056_alpha_dummy_008 f)),
                          ((nb056_alpha_dummy_011), (nb056_alpha_dummy_012 f)),
                          ((nb056_alpha_dummy_003), (nb056_alpha_dummy_004 f)),
                          ((nb056_alpha_dummy_001), (nb056_alpha_dummy_002 f)),
                          ((nb056_alpha_dummy_000), f)]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
