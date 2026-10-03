/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C066C001Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C066C001Part002`. -/


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
noncomputable def nb066_wpp_refl_0000 (x : Var) (y : Var) (A : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) :
    TReflOn [((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] (A).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0000 x y A R dv_A_x dv_A_y)

@[expose]
noncomputable def nb066_split_alpha_0000 (x : Var) (y : Var) (A : Class) (R : Class) :
    TAlphaWff
      [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)),
        ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)),
        ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)),
        ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
        ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
        ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
        ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
        ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
        ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)),
        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb066_alpha_dummy_022 A R))
            (syn_cun (Class.cv (nb066_alpha_dummy_023 A R))
              (Class.cv (nb066_alpha_dummy_024 A R))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb066_alpha_dummy_025 x R))
            (syn_cun (Class.cv (nb066_alpha_dummy_026 x R))
              (Class.cv (nb066_alpha_dummy_027 x R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0018 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0019 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0016 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0017 x R) 0)) (TAlphaVar.there
                              (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0022 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0023 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0020 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0021 x R) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0018 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0019 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0016 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0017 x R) 0)) (TAlphaVar.there
                              (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0022 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0023 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0020 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0021 x R) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)),
          ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)),
          ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)),
          ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
          ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
          ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
          ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
          ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
          ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)),
          ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
          ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
          ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
          ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0026 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0027 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0024 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0025 x R) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0026 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0027 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0024 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0025 x R) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0030 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0031 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0028 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0029 x R) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0030 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0031 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0028 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0029 x R) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb066_split_alpha_0001 (x : Var) (y : Var) (A : Class) (R : Class) :
    TAlphaWff
      [((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
        ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
        ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)),
        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (Wff.imp (Wff.classMem (Class.cv (nb066_alpha_dummy_009 A R))
          (Class.cv (nb066_alpha_dummy_003 A R))) (Wff.neg
          (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
            (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R))))))
      (Wff.imp (Wff.classMem (Class.cv (nb066_alpha_dummy_011 x R))
          (Class.cv (nb066_alpha_dummy_005 x R))) (Wff.neg
          (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
            (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0004 A R) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0006 x R) 0)) (TAlphaVar.there
              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0008 A R) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0009 x R) 0)) (TAlphaVar.there
                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0005 A R) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0007 x R) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
                ((Class.cv (nb066_alpha_dummy_002 A R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
                ((Class.cv (nb066_alpha_dummy_004 x R))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0010 A R) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0011 x R) 0))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0010 A R) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0011 x R) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb066_alpha_dummy_009 A R))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb066_alpha_dummy_011 x R))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb066_support_mem_0014 A R) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb066_support_mem_0015 x R) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb066_support_mem_0014 A R) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb066_support_mem_0015 x R) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb066_support_mem_0013 x R) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb066_alpha_dummy_024 A R),
        (nb066_alpha_dummy_027 x R)), ((nb066_alpha_dummy_023 A R),
        (nb066_alpha_dummy_026 x R)), ((nb066_alpha_dummy_022 A R),
        (nb066_alpha_dummy_025 x R)), ((nb066_alpha_dummy_020 A R),
        (nb066_alpha_dummy_021 x R)), ((nb066_alpha_dummy_016 A R),
        (nb066_alpha_dummy_018 x R)), ((nb066_alpha_dummy_017 A R),
        (nb066_alpha_dummy_019 x R)), ((nb066_alpha_dummy_009 A R),
        (nb066_alpha_dummy_011 x R)), ((nb066_alpha_dummy_008 A R),
        (nb066_alpha_dummy_010 x R)), ((nb066_alpha_dummy_014 A R),
        (nb066_alpha_dummy_015 x R)), ((nb066_alpha_dummy_012 A R),
        (nb066_alpha_dummy_013 x R)), ((nb066_alpha_dummy_003 A R),
        (nb066_alpha_dummy_005 x R)), ((nb066_alpha_dummy_002 A R),
        (nb066_alpha_dummy_004 x R)), ((nb066_alpha_dummy_000 A R), x),
        ((nb066_alpha_dummy_001 A R), y)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb066_split_alpha_0000 x y A R))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt
                                (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
                              ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
                              ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
                              ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                              ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                              ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)),
                              ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                              ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                              ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                              ((nb066_alpha_dummy_000 A R), x),
                              ((nb066_alpha_dummy_001 A R), y)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb066_support_mem_0012 A R) 0)) (Nat.ne_of_lt
                                (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
                              ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
                              ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
                              ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                              ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                              ((nb066_alpha_dummy_014 A R), (nb066_alpha_dummy_015 x R)),
                              ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                              ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                              ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                              ((nb066_alpha_dummy_000 A R), x),
                              ((nb066_alpha_dummy_001 A R), y)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C066C001Part003`. -/


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
noncomputable def nb066_split_alpha_0002 (x : Var) (y : Var) (A : Class) (R : Class) :
    TAlphaWff
      [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)),
        ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)),
        ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)),
        ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
        ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
        ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
        ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)),
        ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
        ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
        ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
        ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb066_alpha_dummy_023 A R))
            (Class.cv (nb066_alpha_dummy_024 A R))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb066_alpha_dummy_022 A R))
            (syn_cun (Class.cv (nb066_alpha_dummy_023 A R))
              (Class.cv (nb066_alpha_dummy_024 A R))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb066_alpha_dummy_026 x R))
            (Class.cv (nb066_alpha_dummy_027 x R))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb066_alpha_dummy_025 x R))
            (syn_cun (Class.cv (nb066_alpha_dummy_026 x R))
              (Class.cv (nb066_alpha_dummy_027 x R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0018 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0019 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0016 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0017 x R) 0)) (TAlphaVar.there
                              (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0022 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0023 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0020 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0021 x R) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0018 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0019 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0016 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0017 x R) 0)) (TAlphaVar.there
                              (freshVar_injective (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0022 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0023 x R) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0020 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0021 x R) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb066_alpha_dummy_024 A R), (nb066_alpha_dummy_027 x R)),
          ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)),
          ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)),
          ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
          ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
          ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
          ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)),
          ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
          ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
          ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
          ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
          ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
          ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
          ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
          ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0026 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0027 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0024 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0025 x R) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0026 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0027 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0024 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0025 x R) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_016 A R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb066_alpha_dummy_018 x R))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0030 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0031 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0028 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0029 x R) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0030 A R) 0)) (Nat.ne_of_lt
                              (mem_lt_freshVar (nb066_support_mem_0031 x R) 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0028 A R) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0029 x R) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb066_split_alpha_0003 (x : Var) (y : Var) (A : Class) (R : Class) :
    TAlphaClass
      [((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)),
        ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
        ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
        ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
        ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (Class.cab (nb066_alpha_dummy_017 A R)
        (syn_wrex (nb066_alpha_dummy_016 A R) (Class.cv (nb066_alpha_dummy_009 A R))
          (Wff.classEq (Class.cv (nb066_alpha_dummy_017 A R))
            (syn_cif (Wff.classMem (Class.cv (nb066_alpha_dummy_016 A R)) (syn_cnnc))
              (syn_cplc (Class.cv (nb066_alpha_dummy_016 A R)) (syn_c1c))
              (Class.cv (nb066_alpha_dummy_016 A R))))))
      (Class.cab (nb066_alpha_dummy_019 x R)
        (syn_wrex (nb066_alpha_dummy_018 x R) (Class.cv (nb066_alpha_dummy_011 x R))
          (Wff.classEq (Class.cv (nb066_alpha_dummy_019 x R))
            (syn_cif (Wff.classMem (Class.cv (nb066_alpha_dummy_018 x R)) (syn_cnnc))
              (syn_cplc (Class.cv (nb066_alpha_dummy_018 x R)) (syn_c1c))
              (Class.cv (nb066_alpha_dummy_018 x R)))))) :=
  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0010 A R) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0011 x R) 0)) (TAlphaVar.there
                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0010 A R) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0011 x R) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0040 A R) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0041 x R) 0))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0038 A R) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0039 x R) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective (((Class.cv (nb066_alpha_dummy_009 A R))).fv)
                (by decide)) (freshVar_injective (((Class.cv (nb066_alpha_dummy_011 x R))).fv)
                (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb066_support_mem_0014 A R) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0015 x R) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb066_support_mem_0014 A R) 0))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb066_support_mem_0015 x R) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb066_support_mem_0012 A R) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed [((nb066_alpha_dummy_024 A R),
                                      (nb066_alpha_dummy_027 x R)),
                                    ((nb066_alpha_dummy_023 A R), (nb066_alpha_dummy_026 x R)),
                                    ((nb066_alpha_dummy_022 A R), (nb066_alpha_dummy_025 x R)),
                                    ((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
                                    ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
                                    ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
                                    ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)),
                                    ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
                                    ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                                    ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                                    ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
                                    ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                                    ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                                    ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                                    ((nb066_alpha_dummy_000 A R), x),
                                    ((nb066_alpha_dummy_001 A R), y)]
                                  (syn_c1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb066_split_alpha_0002 x y A R))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
                        ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
                        ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
                        ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)),
                        ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
                        ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                        ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                        ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
                        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
                      (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0012 A R) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0013 x R) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                      [((nb066_alpha_dummy_020 A R), (nb066_alpha_dummy_021 x R)),
                        ((nb066_alpha_dummy_016 A R), (nb066_alpha_dummy_018 x R)),
                        ((nb066_alpha_dummy_017 A R), (nb066_alpha_dummy_019 x R)),
                        ((nb066_alpha_dummy_042 A R), (nb066_alpha_dummy_043 x R)),
                        ((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
                        ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                        ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                        ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
                        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
                      (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))

@[expose]
noncomputable def nb066_split_alpha_0004 (x : Var) (y : Var) (A : Class) (R : Class) :
    TAlphaWff
      [((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
        ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
        ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (Wff.imp (Wff.classMem (Class.cv (nb066_alpha_dummy_038 A R))
          (Class.cab (nb066_alpha_dummy_008 A R)
            (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb066_alpha_dummy_038 A R))
            (Class.cab (nb066_alpha_dummy_008 A R)
              (syn_wrex (nb066_alpha_dummy_009 A R) (Class.cv (nb066_alpha_dummy_002 A R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_008 A R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_009 A R)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb066_alpha_dummy_039 x R))
          (Class.cab (nb066_alpha_dummy_010 x R)
            (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
              (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb066_alpha_dummy_039 x R))
            (Class.cab (nb066_alpha_dummy_010 x R)
              (syn_wrex (nb066_alpha_dummy_011 x R) (Class.cv (nb066_alpha_dummy_004 x R))
                (Wff.classEq (Class.cv (nb066_alpha_dummy_010 x R))
                  (syn_cun (syn_cphi (Class.cv (nb066_alpha_dummy_011 x R)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 1))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 0))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0036 A R) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0037 x R) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0033 A R) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0035 x R) 0))
                        (TAlphaVar.there (freshVar_injective ((R).fv ∪
                              ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv)
                            (by decide))
                          (freshVar_injective ((R).fv ∪ ((syn_csn (Class.cv x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
                      ((Class.cv (nb066_alpha_dummy_002 A R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
                      ((Class.cv (nb066_alpha_dummy_004 x R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb066_split_alpha_0003 x y A R))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (nb066_split_alpha_0003 x y A R))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
                          ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                          ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                          ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
                          ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                          ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                          ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                          ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 1))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0032 A R) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0034 x R) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0036 A R) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0037 x R) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0033 A R) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0035 x R) 0))
                          (TAlphaVar.there (freshVar_injective ((R).fv ∪
                                ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv)
                              (by decide))
                            (freshVar_injective ((R).fv ∪ ((syn_csn (Class.cv x))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb066_alpha_dummy_003 A R))).fv ∪
                        ((Class.cv (nb066_alpha_dummy_002 A R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb066_alpha_dummy_005 x R))).fv ∪
                        ((Class.cv (nb066_alpha_dummy_004 x R))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (nb066_split_alpha_0003 x y A R))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (nb066_split_alpha_0003 x y A R))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb066_alpha_dummy_040 A R), (nb066_alpha_dummy_041 x R)),
                            ((nb066_alpha_dummy_009 A R), (nb066_alpha_dummy_011 x R)),
                            ((nb066_alpha_dummy_008 A R), (nb066_alpha_dummy_010 x R)),
                            ((nb066_alpha_dummy_038 A R), (nb066_alpha_dummy_039 x R)),
                            ((nb066_alpha_dummy_012 A R), (nb066_alpha_dummy_013 x R)),
                            ((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                            ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                            ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb066_focused_notmem_0002 (A : Class) (R : Class) :
    (nb066_alpha_dummy_003 A R) ∉ R.fv :=
  by
  change
    freshVar ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0118 (A : Class) (R : Class) :
    (nb066_alpha_dummy_003 A R) ∉ (R).fv := by exact (nb066_focused_notmem_0002 A R)

theorem nb066_focused_notmem_0003 (x : Var) (R : Class) :
    (nb066_alpha_dummy_005 x R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ ((syn_csn (Class.cv x))).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0119 (x : Var) (R : Class) :
    (nb066_alpha_dummy_005 x R) ∉ (R).fv := by exact (nb066_focused_notmem_0003 x R)

theorem nb066_focused_notmem_0004 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ∉ R.fv :=
  by
  change
    freshVar ((R).fv ∪ ((syn_csn (Class.cv (nb066_alpha_dummy_000 A R)))).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0120 (A : Class) (R : Class) :
    (nb066_alpha_dummy_002 A R) ∉ (R).fv := by exact (nb066_focused_notmem_0004 A R)

theorem nb066_focused_notmem_0005 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ ((syn_csn (Class.cv x))).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb066_wpp_notmem_0121 (x : Var) (R : Class) :
    (nb066_alpha_dummy_004 x R) ∉ (R).fv := by exact (nb066_focused_notmem_0005 x R)

theorem nb066_focused_notmem_0006 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∉ R.fv :=
  by
  change freshVar ((A).fv ∪ (R).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb066_wpp_notmem_0122 (A : Class) (R : Class) :
    (nb066_alpha_dummy_000 A R) ∉ (R).fv := by exact (nb066_focused_notmem_0006 A R)

theorem nb066_wpp_notmem_0123 (x : Var) (R : Class) (dv_R_x : x ∉ R.fv) : x ∉ (R).fv := by
  exact dv_R_x

theorem nb066_focused_notmem_0007 (A : Class) (R : Class) :
    (nb066_alpha_dummy_001 A R) ∉ R.fv :=
  by
  change freshVar ((A).fv ∪ (R).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb066_wpp_notmem_0124 (A : Class) (R : Class) :
    (nb066_alpha_dummy_001 A R) ∉ (R).fv := by exact (nb066_focused_notmem_0007 A R)

theorem nb066_wpp_notmem_0125 (y : Var) (R : Class) (dv_R_y : y ∉ R.fv) : y ∉ (R).fv := by
  exact dv_R_y

theorem nb066_compact_envfresh_0008 (x : Var) (y : Var) (A : Class) (R : Class)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TEnvFresh
      [((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (R).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb066_alpha_dummy_003 A R) (nb066_alpha_dummy_005 x R)
      (nb066_wpp_notmem_0118 A R) (nb066_wpp_notmem_0119 x R)
      (TEnvFresh.consFresh (nb066_alpha_dummy_002 A R) (nb066_alpha_dummy_004 x R)
        (nb066_wpp_notmem_0120 A R) (nb066_wpp_notmem_0121 x R)
        (TEnvFresh.consFresh (nb066_alpha_dummy_000 A R) x (nb066_wpp_notmem_0122 A R)
          (nb066_wpp_notmem_0123 x R dv_R_x)
          (TEnvFresh.consFresh (nb066_alpha_dummy_001 A R) y (nb066_wpp_notmem_0124 A R)
            (nb066_wpp_notmem_0125 y R dv_R_y) (TEnvFresh.nil (R).fv)))))

@[expose]
noncomputable def nb066_wpp_refl_0008 (x : Var) (y : Var) (A : Class) (R : Class)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TReflOn
      [((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
        ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
        ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
      (R).fv :=
  TEnvFresh.reflOn (nb066_compact_envfresh_0008 x y A R dv_R_x dv_R_y)

@[expose]
noncomputable def nominal_df_qs (x : Var) (y : Var) (A : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cqs A R) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) R))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn
                [((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)] A
                (nb066_wpp_refl_0000 x y A R dv_A_x dv_A_y))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective ((A).fv ∪ (R).fv) (by decide))
                  (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb066_support_mem_0002 A R) 0)) (Nat.ne_of_lt
                                (mem_lt_freshVar (nb066_support_mem_0003 x) 0)) (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0000 A R) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (nb066_support_mem_0001 x R) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb066_support_mem_0000 A R) 0))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb066_support_mem_0001 x R) 0))
                                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb066_split_alpha_0001 x y A R))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.neg
        (nb066_split_alpha_0001 x y A R)))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb066_split_alpha_0004 x y A R))))))))
                      (TAlphaClass.refl_of_reflOn
                        [((nb066_alpha_dummy_003 A R), (nb066_alpha_dummy_005 x R)),
                          ((nb066_alpha_dummy_002 A R), (nb066_alpha_dummy_004 x R)),
                          ((nb066_alpha_dummy_000 A R), x), ((nb066_alpha_dummy_001 A R), y)]
                        R (nb066_wpp_refl_0008 x y A R dv_R_x dv_R_y))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
