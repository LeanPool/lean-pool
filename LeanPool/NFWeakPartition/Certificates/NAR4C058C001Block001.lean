/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C058C001Part002Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C058C001Part002`. -/


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
noncomputable def nb058_split_alpha_0000 (x : Var) :
    TAlphaWff
      [((nb058_alpha_dummy_021), (nb058_alpha_dummy_024 x)),
        ((nb058_alpha_dummy_020), (nb058_alpha_dummy_023 x)),
        ((nb058_alpha_dummy_019), (nb058_alpha_dummy_022 x)),
        ((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
        ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
        ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
        ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
        ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
        ((nb058_alpha_dummy_011), (nb058_alpha_dummy_012 x)),
        ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
        ((nb058_alpha_dummy_000), x),
        ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb058_alpha_dummy_019))
            (syn_cun (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb058_alpha_dummy_022 x))
            (syn_cun (Class.cv (nb058_alpha_dummy_023 x))
              (Class.cv (nb058_alpha_dummy_024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb058_alpha_dummy_021), (nb058_alpha_dummy_024 x)),
          ((nb058_alpha_dummy_020), (nb058_alpha_dummy_023 x)),
          ((nb058_alpha_dummy_019), (nb058_alpha_dummy_022 x)),
          ((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
          ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
          ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
          ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
          ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
          ((nb058_alpha_dummy_011), (nb058_alpha_dummy_012 x)),
          ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
          ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)), ((nb058_alpha_dummy_000), x),
          ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb058_split_alpha_0001 (x : Var) :
    TAlphaWff
      [((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
        ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
        ((nb058_alpha_dummy_011), (nb058_alpha_dummy_012 x)),
        ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
        ((nb058_alpha_dummy_000), x),
        ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb058_alpha_dummy_006))
          (Class.cv (nb058_alpha_dummy_000))) (Wff.neg
          (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
            (syn_cphi (Class.cv (nb058_alpha_dummy_006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb058_alpha_dummy_008 x)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
            (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0010) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0011 x) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0007) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0009 x) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0004) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0005 x) 0))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb058_alpha_dummy_000))).fv ∪
                ((Class.cv (nb058_alpha_dummy_001))).fv) (by decide)) (freshVar_injective
              (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb058_alpha_dummy_006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb058_alpha_dummy_008 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0016) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0017 x) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0016) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb058_alpha_dummy_021),
        (nb058_alpha_dummy_024 x)), ((nb058_alpha_dummy_020), (nb058_alpha_dummy_023 x)),
        ((nb058_alpha_dummy_019), (nb058_alpha_dummy_022 x)), ((nb058_alpha_dummy_017),
        (nb058_alpha_dummy_018 x)), ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
        ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)), ((nb058_alpha_dummy_006),
        (nb058_alpha_dummy_008 x)), ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
        ((nb058_alpha_dummy_011), (nb058_alpha_dummy_012 x)), ((nb058_alpha_dummy_009),
        (nb058_alpha_dummy_010 x)), ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
        ((nb058_alpha_dummy_000), x), ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb058_split_alpha_0000 x))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
                              ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
                              ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
                              ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                              ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                              ((nb058_alpha_dummy_011), (nb058_alpha_dummy_012 x)),
                              ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                              ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                              ((nb058_alpha_dummy_000), x),
                              ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
                              ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
                              ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
                              ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                              ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                              ((nb058_alpha_dummy_011), (nb058_alpha_dummy_012 x)),
                              ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                              ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                              ((nb058_alpha_dummy_000), x),
                              ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C058C001Part003`. -/


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
noncomputable def nb058_split_alpha_0002 (x : Var) :
    TAlphaWff
      [((nb058_alpha_dummy_021), (nb058_alpha_dummy_024 x)),
        ((nb058_alpha_dummy_020), (nb058_alpha_dummy_023 x)),
        ((nb058_alpha_dummy_019), (nb058_alpha_dummy_022 x)),
        ((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
        ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
        ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
        ((nb058_alpha_dummy_039), (nb058_alpha_dummy_040 x)),
        ((nb058_alpha_dummy_037), (nb058_alpha_dummy_038 x)),
        ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
        ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
        ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
        ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
        ((nb058_alpha_dummy_000), x),
        ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb058_alpha_dummy_019))
            (syn_cun (Class.cv (nb058_alpha_dummy_020)) (Class.cv (nb058_alpha_dummy_021))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb058_alpha_dummy_023 x))
            (Class.cv (nb058_alpha_dummy_024 x))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb058_alpha_dummy_022 x))
            (syn_cun (Class.cv (nb058_alpha_dummy_023 x))
              (Class.cv (nb058_alpha_dummy_024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb058_alpha_dummy_021), (nb058_alpha_dummy_024 x)),
          ((nb058_alpha_dummy_020), (nb058_alpha_dummy_023 x)),
          ((nb058_alpha_dummy_019), (nb058_alpha_dummy_022 x)),
          ((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
          ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
          ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
          ((nb058_alpha_dummy_039), (nb058_alpha_dummy_040 x)),
          ((nb058_alpha_dummy_037), (nb058_alpha_dummy_038 x)),
          ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
          ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
          ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
          ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
          ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)), ((nb058_alpha_dummy_000), x),
          ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb058_split_alpha_0003 (x : Var) :
    TAlphaWff
      [((nb058_alpha_dummy_039), (nb058_alpha_dummy_040 x)),
        ((nb058_alpha_dummy_037), (nb058_alpha_dummy_038 x)),
        ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
        ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
        ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
        ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
        ((nb058_alpha_dummy_000), x),
        ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
      (Wff.classMem (Class.cv (nb058_alpha_dummy_039))
        (syn_cphi (Class.cv (nb058_alpha_dummy_006))))
      (Wff.classMem (Class.cv (nb058_alpha_dummy_040 x))
        (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0042) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0043 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0041 x) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb058_alpha_dummy_006))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb058_alpha_dummy_008 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0016) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0017 x) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0016) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0017 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb058_alpha_dummy_021), (nb058_alpha_dummy_024 x)),
                                      ((nb058_alpha_dummy_020), (nb058_alpha_dummy_023 x)),
                                      ((nb058_alpha_dummy_019), (nb058_alpha_dummy_022 x)),
                                      ((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
                                      ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
                                      ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
                                      ((nb058_alpha_dummy_039), (nb058_alpha_dummy_040 x)),
                                      ((nb058_alpha_dummy_037), (nb058_alpha_dummy_038 x)),
                                      ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                                      ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                                      ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
                                      ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                                      ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                                      ((nb058_alpha_dummy_000), x), ((nb058_alpha_dummy_003),
                                        (nb058_alpha_dummy_004 x))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb058_split_alpha_0002 x))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
                          ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
                          ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
                          ((nb058_alpha_dummy_039), (nb058_alpha_dummy_040 x)),
                          ((nb058_alpha_dummy_037), (nb058_alpha_dummy_038 x)),
                          ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                          ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                          ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
                          ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                          ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                          ((nb058_alpha_dummy_000), x),
                          ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb058_alpha_dummy_017), (nb058_alpha_dummy_018 x)),
                          ((nb058_alpha_dummy_013), (nb058_alpha_dummy_015 x)),
                          ((nb058_alpha_dummy_014), (nb058_alpha_dummy_016 x)),
                          ((nb058_alpha_dummy_039), (nb058_alpha_dummy_040 x)),
                          ((nb058_alpha_dummy_037), (nb058_alpha_dummy_038 x)),
                          ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                          ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                          ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
                          ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                          ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                          ((nb058_alpha_dummy_000), x),
                          ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb058_split_alpha_0004 (x : Var) :
    TAlphaWff
      [((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)), ((nb058_alpha_dummy_000), x),
        ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
      (Wff.classEq (Class.cv (nb058_alpha_dummy_003))
        (syn_cop (Class.cv (nb058_alpha_dummy_000)) (Class.cv (nb058_alpha_dummy_001))))
      (Wff.classEq (Class.cv (nb058_alpha_dummy_004 x))
        (syn_cop (Class.cv x) (Class.cv (nb058_alpha_dummy_002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0002) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0003 x) 0))) (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0000) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0001 x) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb058_split_alpha_0001 x)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb058_split_alpha_0001 x)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0034) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0034) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0038) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0039 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0035) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0037 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb058_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb058_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb058_split_alpha_0003 x)
        (nb058_split_alpha_0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb058_alpha_dummy_037),
        (nb058_alpha_dummy_038 x)), ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                                        ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                                        ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
                                        ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                                        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                                        ((nb058_alpha_dummy_000), x), ((nb058_alpha_dummy_003),
        (nb058_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0034) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0034) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0038) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0039 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0035) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0037 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058_alpha_dummy_000))).fv ∪
                                    ((Class.cv (nb058_alpha_dummy_001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb058_alpha_dummy_002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb058_split_alpha_0003 x)
        (nb058_split_alpha_0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb058_alpha_dummy_037),
        (nb058_alpha_dummy_038 x)), ((nb058_alpha_dummy_006), (nb058_alpha_dummy_008 x)),
                                        ((nb058_alpha_dummy_005), (nb058_alpha_dummy_007 x)),
                                        ((nb058_alpha_dummy_035), (nb058_alpha_dummy_036 x)),
                                        ((nb058_alpha_dummy_009), (nb058_alpha_dummy_010 x)),
                                        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                                        ((nb058_alpha_dummy_000), x), ((nb058_alpha_dummy_003),
        (nb058_alpha_dummy_004 x))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

@[expose]
noncomputable def nb058_split_alpha_0005 (x : Var) :
    TAlphaWff
      [((nb058_alpha_dummy_043), (nb058_alpha_dummy_044 x)),
        ((nb058_alpha_dummy_041), (nb058_alpha_dummy_042 x)),
        ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
        ((nb058_alpha_dummy_000), x),
        ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
      (Wff.classMem (Class.cv (nb058_alpha_dummy_043))
        (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))))
      (Wff.classMem (Class.cv (nb058_alpha_dummy_044 x)) (syn_cpw (syn_cuni (Class.cv x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0046) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0047 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0044) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0045 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb058_alpha_dummy_000))).fv) (by decide))
                                  (freshVar_injective (((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0058) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0059 x) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0058) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0059 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0056) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0057 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0054) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0051 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0049 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0046) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0047 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0044) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0045 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb058_alpha_dummy_000))).fv) (by decide))
                                  (freshVar_injective (((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0058) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0059 x) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0058) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0059 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0056) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0057 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0054) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0051 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0049 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _))))))))))))))))))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _)))))

@[expose]
noncomputable def nominal_df_pw1fn (x : Var) :
    Nominal.NPrf
      (.classEq (syn_cpw1fn) (syn_cmpt x (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb058_split_alpha_0004 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0004) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0005 x) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                      ((nb058_alpha_dummy_000), x),
                      ((nb058_alpha_dummy_003), (nb058_alpha_dummy_004 x))]
                    (syn_c1c) (by simp only [fv_syn_c1c])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (nb058_split_alpha_0005 x) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb058_alpha_dummy_043), (nb058_alpha_dummy_044 x)),
                                      ((nb058_alpha_dummy_041), (nb058_alpha_dummy_042 x)),
                                      ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                                      ((nb058_alpha_dummy_000), x), ((nb058_alpha_dummy_003),
                                        (nb058_alpha_dummy_004 x))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (nb058_split_alpha_0005 x) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed
                                    [((nb058_alpha_dummy_043), (nb058_alpha_dummy_044 x)),
                                      ((nb058_alpha_dummy_041), (nb058_alpha_dummy_042 x)),
                                      ((nb058_alpha_dummy_001), (nb058_alpha_dummy_002 x)),
                                      ((nb058_alpha_dummy_000), x), ((nb058_alpha_dummy_003),
                                        (nb058_alpha_dummy_004 x))]
                                    (syn_c1c) (by simp only [fv_syn_c1c]))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
