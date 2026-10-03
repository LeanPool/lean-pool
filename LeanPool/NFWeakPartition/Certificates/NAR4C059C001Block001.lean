/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C059C001Part002Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C059C001Part002`. -/


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
noncomputable def nb059_wpp_refl_0001 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) :
    TReflOn
      [((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (S_cls).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0001 R S_cls a dv_S_a)

@[expose]
noncomputable def nb059_split_alpha_0000 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)),
        ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)),
        ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)),
        ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
        ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
        ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
        ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
        ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
        ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
        ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_031 R S_cls))
            (syn_cun (Class.cv (nb059_alpha_dummy_032 R S_cls))
              (Class.cv (nb059_alpha_dummy_033 R S_cls))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_034 R a))
            (syn_cun (Class.cv (nb059_alpha_dummy_035 R a))
              (Class.cv (nb059_alpha_dummy_036 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0024 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0022 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0024 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0022 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)),
          ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)),
          ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)),
          ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
          ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
          ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
          ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
          ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
          ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
          ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
          ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
          ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
          ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
          ((nb059_alpha_dummy_000 R S_cls), a),
          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0036 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0034 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0035 R a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0036 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0034 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0035 R a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C059C001Part003`. -/


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
noncomputable def nb059_split_alpha_0001 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
        ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
        ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
        ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
        (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))
      (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
        (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
            ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) (by decide)) (freshVar_injective
          (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
            ((Class.cv (nb059_alpha_dummy_015 R a))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv)
                  (by decide)) (freshVar_injective (((Class.cv (nb059_alpha_dummy_020 R a))).fv)
                  (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0020 R S_cls) 1))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0021 R a) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0020 R S_cls) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb059_support_mem_0021 R a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.refl_of_closed [((nb059_alpha_dummy_033 R S_cls),
                                        (nb059_alpha_dummy_036 R a)),
                                      ((nb059_alpha_dummy_032 R S_cls),
                                        (nb059_alpha_dummy_035 R a)),
                                      ((nb059_alpha_dummy_031 R S_cls),
                                        (nb059_alpha_dummy_034 R a)),
                                      ((nb059_alpha_dummy_029 R S_cls),
                                        (nb059_alpha_dummy_030 R a)),
                                      ((nb059_alpha_dummy_025 R S_cls),
                                        (nb059_alpha_dummy_027 R a)),
                                      ((nb059_alpha_dummy_026 R S_cls),
                                        (nb059_alpha_dummy_028 R a)),
                                      ((nb059_alpha_dummy_018 R S_cls),
                                        (nb059_alpha_dummy_020 R a)),
                                      ((nb059_alpha_dummy_017 R S_cls),
                                        (nb059_alpha_dummy_019 R a)),
                                      ((nb059_alpha_dummy_023 R S_cls),
                                        (nb059_alpha_dummy_024 R a)),
                                      ((nb059_alpha_dummy_021 R S_cls),
                                        (nb059_alpha_dummy_022 R a)),
                                      ((nb059_alpha_dummy_014 R S_cls),
                                        (nb059_alpha_dummy_016 R a)),
                                      ((nb059_alpha_dummy_013 R S_cls),
                                        (nb059_alpha_dummy_015 R a)),
                                      ((nb059_alpha_dummy_011 R S_cls),
                                        (nb059_alpha_dummy_012 R a)),
                                      ((nb059_alpha_dummy_009 R S_cls),
                                        (nb059_alpha_dummy_010 R a)),
                                      ((nb059_alpha_dummy_000 R S_cls), a),
                                      ((nb059_alpha_dummy_002 R S_cls),
                                        (nb059_alpha_dummy_004 R S_cls a)),
                                      ((nb059_alpha_dummy_001 R S_cls),
                                        (nb059_alpha_dummy_003 R S_cls a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb059_split_alpha_0000 R S_cls a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
                          ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
                          ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
                          ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
                          ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
                          ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
                          ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
                          ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                          ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
                          ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
                          ((nb059_alpha_dummy_000 R S_cls), a),
                          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
                          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
                          ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
                          ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
                          ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
                          ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
                          ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
                          ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
                          ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                          ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
                          ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
                          ((nb059_alpha_dummy_000 R S_cls), a),
                          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
                          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb059_split_alpha_0002 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)),
        ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)),
        ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)),
        ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
        ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
        ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
        ((nb059_alpha_dummy_051 R S_cls), (nb059_alpha_dummy_052 R a)),
        ((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
        ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
        ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
        ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
        ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_031 R S_cls))
            (syn_cun (Class.cv (nb059_alpha_dummy_032 R S_cls))
              (Class.cv (nb059_alpha_dummy_033 R S_cls))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_034 R a))
            (syn_cun (Class.cv (nb059_alpha_dummy_035 R a))
              (Class.cv (nb059_alpha_dummy_036 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0024 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0022 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0024 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0025 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0022 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0023 R a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                  ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb059_alpha_dummy_033 R S_cls), (nb059_alpha_dummy_036 R a)),
          ((nb059_alpha_dummy_032 R S_cls), (nb059_alpha_dummy_035 R a)),
          ((nb059_alpha_dummy_031 R S_cls), (nb059_alpha_dummy_034 R a)),
          ((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
          ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
          ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
          ((nb059_alpha_dummy_051 R S_cls), (nb059_alpha_dummy_052 R a)),
          ((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
          ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
          ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
          ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
          ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
          ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
          ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
          ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
          ((nb059_alpha_dummy_000 R S_cls), a),
          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪
                                    ((syn_c1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0036 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0034 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0035 R a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0036 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0037 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0034 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0035 R a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def nb059_split_alpha_0003 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
        ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
        ((nb059_alpha_dummy_051 R S_cls), (nb059_alpha_dummy_052 R a)),
        ((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
        ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
        ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
        ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
        ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_025 R S_cls))
          (Class.cv (nb059_alpha_dummy_018 R S_cls))) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_026 R S_cls))
            (syn_cif (Wff.classMem (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_cnnc))
              (syn_cplc (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_c1c))
              (Class.cv (nb059_alpha_dummy_025 R S_cls))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_027 R a))
          (Class.cv (nb059_alpha_dummy_020 R a))) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_028 R a))
            (syn_cif (Wff.classMem (Class.cv (nb059_alpha_dummy_027 R a)) (syn_cnnc))
              (syn_cplc (Class.cv (nb059_alpha_dummy_027 R a)) (syn_c1c))
              (Class.cv (nb059_alpha_dummy_027 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 0)) (TAlphaVar.there
            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 1)) (TAlphaVar.there
              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0046 R S_cls) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0047 R a) 0)) (TAlphaVar.there
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0044 R S_cls) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0045 R a) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv)
              (by decide))
            (freshVar_injective (((Class.cv (nb059_alpha_dummy_020 R a))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0020 R S_cls) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0021 R a) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb059_support_mem_0020 R S_cls) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0021 R a) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.refl_of_closed [((nb059_alpha_dummy_033 R S_cls),
                                    (nb059_alpha_dummy_036 R a)),
                                  ((nb059_alpha_dummy_032 R S_cls),
                                    (nb059_alpha_dummy_035 R a)),
                                  ((nb059_alpha_dummy_031 R S_cls),
                                    (nb059_alpha_dummy_034 R a)),
                                  ((nb059_alpha_dummy_029 R S_cls),
                                    (nb059_alpha_dummy_030 R a)),
                                  ((nb059_alpha_dummy_025 R S_cls),
                                    (nb059_alpha_dummy_027 R a)),
                                  ((nb059_alpha_dummy_026 R S_cls),
                                    (nb059_alpha_dummy_028 R a)),
                                  ((nb059_alpha_dummy_051 R S_cls),
                                    (nb059_alpha_dummy_052 R a)),
                                  ((nb059_alpha_dummy_049 R S_cls),
                                    (nb059_alpha_dummy_050 R a)),
                                  ((nb059_alpha_dummy_018 R S_cls),
                                    (nb059_alpha_dummy_020 R a)),
                                  ((nb059_alpha_dummy_017 R S_cls),
                                    (nb059_alpha_dummy_019 R a)),
                                  ((nb059_alpha_dummy_047 R S_cls),
                                    (nb059_alpha_dummy_048 R a)),
                                  ((nb059_alpha_dummy_021 R S_cls),
                                    (nb059_alpha_dummy_022 R a)),
                                  ((nb059_alpha_dummy_014 R S_cls),
                                    (nb059_alpha_dummy_016 R a)),
                                  ((nb059_alpha_dummy_013 R S_cls),
                                    (nb059_alpha_dummy_015 R a)),
                                  ((nb059_alpha_dummy_011 R S_cls),
                                    (nb059_alpha_dummy_012 R a)),
                                  ((nb059_alpha_dummy_009 R S_cls),
                                    (nb059_alpha_dummy_010 R a)),
                                  ((nb059_alpha_dummy_000 R S_cls), a),
                                  ((nb059_alpha_dummy_002 R S_cls),
                                    (nb059_alpha_dummy_004 R S_cls a)),
                                  ((nb059_alpha_dummy_001 R S_cls),
                                    (nb059_alpha_dummy_003 R S_cls a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb059_split_alpha_0002 R S_cls a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
                      ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
                      ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
                      ((nb059_alpha_dummy_051 R S_cls), (nb059_alpha_dummy_052 R a)),
                      ((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
                      ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
                      ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
                      ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
                      ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
                      ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                      ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                      ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
                      ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
                      ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls),
                        (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls),
                        (nb059_alpha_dummy_003 R S_cls a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb059_alpha_dummy_029 R S_cls), (nb059_alpha_dummy_030 R a)),
                      ((nb059_alpha_dummy_025 R S_cls), (nb059_alpha_dummy_027 R a)),
                      ((nb059_alpha_dummy_026 R S_cls), (nb059_alpha_dummy_028 R a)),
                      ((nb059_alpha_dummy_051 R S_cls), (nb059_alpha_dummy_052 R a)),
                      ((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
                      ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
                      ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
                      ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
                      ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
                      ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                      ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                      ((nb059_alpha_dummy_011 R S_cls), (nb059_alpha_dummy_012 R a)),
                      ((nb059_alpha_dummy_009 R S_cls), (nb059_alpha_dummy_010 R a)),
                      ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls),
                        (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls),
                        (nb059_alpha_dummy_003 R S_cls a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
