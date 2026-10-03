/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C057C001Part007Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C057C001Part007`. -/


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
noncomputable def nb057_split_alpha_0000 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)),
        ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
        ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)),
        ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
        ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
        ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
        ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
        ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)),
        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_018))
            (syn_cun (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_021 f a))
            (syn_cun (Class.cv (nb057_alpha_dummy_022 f a))
              (Class.cv (nb057_alpha_dummy_023 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)),
          ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
          ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)),
          ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
          ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
          ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
          ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
          ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
          ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)),
          ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part008`. -/


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
noncomputable def nb057_split_alpha_0001 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
        ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)),
        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_005))
          (Class.cv (nb057_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
            (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_007 f a)) (Class.cv f)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
            (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0009 f a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0007 f a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_f) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_001))).fv ∪
                ((Class.cv (nb057_alpha_dummy_000))).fv) (by decide))
            (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0015 f a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0015 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb057_alpha_dummy_020),
        (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
        ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016),
        (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
        ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_005),
        (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
        ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)), ((nb057_alpha_dummy_008),
        (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a),
        ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb057_split_alpha_0000 f a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                              ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                              ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                              ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                              ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                              ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)),
                              ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                              ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                              ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                              ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                              ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                              ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                              ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                              ((nb057_alpha_dummy_010), (nb057_alpha_dummy_011 f a)),
                              ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                              ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                              ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0002 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)),
        ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
        ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)),
        ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
        ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
        ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
        ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
        ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
        ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
        ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_018))
            (syn_cun (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_021 f a))
            (syn_cun (Class.cv (nb057_alpha_dummy_022 f a))
              (Class.cv (nb057_alpha_dummy_023 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0019 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0017 f a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0023 f a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0021 f a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_020), (nb057_alpha_dummy_023 f a)),
          ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
          ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)),
          ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
          ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
          ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
          ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
          ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
          ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
          ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
          ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
          ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0027 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0025 f a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0031 f a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0029 f a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0003 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
        ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
        ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
        ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_038))
          (syn_cphi (Class.cv (nb057_alpha_dummy_005)))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_038))
            (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_039 f a))
          (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_039 f a))
            (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0041 f a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0039 f a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0015 f a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0015 f a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb057_alpha_dummy_020),
        (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
                                        ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)),
                                        ((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                                        ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                                        ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                                        ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
                                        ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
                                        ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                                        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                                        ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                                        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                                        ((nb057_alpha_dummy_000), a),
                                        ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
        (nb057_alpha_dummy_003 f a))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb057_split_alpha_0002 f a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                            ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                            ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                            ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
                            ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
                            ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                            ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                            ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                            ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                            ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                            ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                            ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
                            ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
                            ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                            ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                            ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                            ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0011 f a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0041 f a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0039 f a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0015 f a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0015 f a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0013 f a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb057_alpha_dummy_020),
        (nb057_alpha_dummy_023 f a)), ((nb057_alpha_dummy_019), (nb057_alpha_dummy_022 f a)),
        ((nb057_alpha_dummy_018), (nb057_alpha_dummy_021 f a)), ((nb057_alpha_dummy_016),
        (nb057_alpha_dummy_017 f a)), ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
        ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)), ((nb057_alpha_dummy_038),
        (nb057_alpha_dummy_039 f a)), ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
        ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)), ((nb057_alpha_dummy_004),
        (nb057_alpha_dummy_006 f a)), ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)), ((nb057_alpha_dummy_000), a),
        ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb057_split_alpha_0002 f a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                              ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                              ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                              ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
                              ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
                              ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                              ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                              ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                              ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                              ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                              ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0013 f a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb057_alpha_dummy_016), (nb057_alpha_dummy_017 f a)),
                              ((nb057_alpha_dummy_012), (nb057_alpha_dummy_014 f a)),
                              ((nb057_alpha_dummy_013), (nb057_alpha_dummy_015 f a)),
                              ((nb057_alpha_dummy_038), (nb057_alpha_dummy_039 f a)),
                              ((nb057_alpha_dummy_036), (nb057_alpha_dummy_037 f a)),
                              ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                              ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                              ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                              ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                              ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                              ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb057_ordered_pair_binder_occurrence (f a : Var) :
    TAlphaClass
      [(nb057_alpha_dummy_000, a), (nb057_alpha_dummy_001, f),
        (nb057_alpha_dummy_002, (nb057_alpha_dummy_003 f a))]
      (Class.cv nb057_alpha_dummy_002) (Class.cv (nb057_alpha_dummy_003 f a)) :=
  by
  have freshness0 : nb057_alpha_dummy_002 ≠ nb057_alpha_dummy_000 :=
    by
    unfold nb057_alpha_dummy_002
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0002) 0)))
  have freshness1 : (nb057_alpha_dummy_003 f a) ≠ a :=
    by
    unfold nb057_alpha_dummy_003
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0003 f a) 0)))
  have freshness2 : nb057_alpha_dummy_002 ≠ nb057_alpha_dummy_001 :=
    by
    unfold nb057_alpha_dummy_002
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0000) 0)))
  have freshness3 : (nb057_alpha_dummy_003 f a) ≠ f :=
    by
    unfold nb057_alpha_dummy_003
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0001 f a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb057_split_alpha_0004 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.classEq (Class.cv (nb057_alpha_dummy_002))
        (syn_cop (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000))))
      (Wff.classEq (Class.cv (nb057_alpha_dummy_003 f a))
        (syn_cop (Class.cv f) (Class.cv a))) :=
  (TAlphaWff.classEq (nb057_ordered_pair_binder_occurrence f a) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0001 f a dv_a_f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0001 f a dv_a_f)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0037 f a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0035 f a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb057_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb057_split_alpha_0003 f a)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb057_alpha_dummy_036),
        (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                                        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                                        ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                                        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                                        ((nb057_alpha_dummy_000), a),
                                        ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
        (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0037 f a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0035 f a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_001))).fv ∪
                                    ((Class.cv (nb057_alpha_dummy_000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb057_split_alpha_0003 f a)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb057_alpha_dummy_036),
        (nb057_alpha_dummy_037 f a)), ((nb057_alpha_dummy_005), (nb057_alpha_dummy_007 f a)),
                                        ((nb057_alpha_dummy_004), (nb057_alpha_dummy_006 f a)),
                                        ((nb057_alpha_dummy_034), (nb057_alpha_dummy_035 f a)),
                                        ((nb057_alpha_dummy_008), (nb057_alpha_dummy_009 f a)),
                                        ((nb057_alpha_dummy_000), a),
                                        ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
        (nb057_alpha_dummy_003 f a))] (syn_ccompl (syn_csn (syn_c0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

theorem nb057_compact_fv_empty_0058 : (nb057_alpha_dummy_042) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0059 (f : Var) :
    (nb057_alpha_dummy_043 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0060 : (nb057_alpha_dummy_040) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0061 (f : Var) :
    (nb057_alpha_dummy_041 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
