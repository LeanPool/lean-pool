/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C059C001Part004

/-! NF weak partition development: NAR4C059C001Part005. -/


public section


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
noncomputable def nb059_split_alpha_0007 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
        ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
        ((nb059_alpha_dummy_023 R S_cls), (nb059_alpha_dummy_024 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_018 R S_cls))
          (Class.cv (nb059_alpha_dummy_014 R S_cls))) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
            (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_020 R a))
          (Class.cv (nb059_alpha_dummy_016 R a))) (Wff.neg
          (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
            (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 1)) (TAlphaVar.there
            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 0)) (TAlphaVar.there
              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0014 R S_cls) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0015 R a) 0)) (TAlphaVar.there
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0011 R S_cls) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0013 R a) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
                ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
                ((Class.cv (nb059_alpha_dummy_015 R a))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 0))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb059_alpha_dummy_020 R a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0020 R S_cls) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb059_support_mem_0021 R a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0020 R S_cls) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb059_support_mem_0021 R a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb059_support_mem_0019 R a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb059_alpha_dummy_033 R S_cls),
        (nb059_alpha_dummy_036 R a)), ((nb059_alpha_dummy_032 R S_cls),
        (nb059_alpha_dummy_035 R a)), ((nb059_alpha_dummy_031 R S_cls),
        (nb059_alpha_dummy_034 R a)), ((nb059_alpha_dummy_029 R S_cls),
        (nb059_alpha_dummy_030 R a)), ((nb059_alpha_dummy_025 R S_cls),
        (nb059_alpha_dummy_027 R a)), ((nb059_alpha_dummy_026 R S_cls),
        (nb059_alpha_dummy_028 R a)), ((nb059_alpha_dummy_018 R S_cls),
        (nb059_alpha_dummy_020 R a)), ((nb059_alpha_dummy_017 R S_cls),
        (nb059_alpha_dummy_019 R a)), ((nb059_alpha_dummy_023 R S_cls),
        (nb059_alpha_dummy_024 R a)), ((nb059_alpha_dummy_021 R S_cls),
        (nb059_alpha_dummy_022 R a)), ((nb059_alpha_dummy_014 R S_cls),
        (nb059_alpha_dummy_016 R a)), ((nb059_alpha_dummy_013 R S_cls),
        (nb059_alpha_dummy_015 R a)), ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.neg
                                      (nb059_split_alpha_0006 R S_cls a))))))))
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
                              ((nb059_alpha_dummy_000 R S_cls), a),
                              ((nb059_alpha_dummy_002 R S_cls),
                                (nb059_alpha_dummy_004 R S_cls a)),
                              ((nb059_alpha_dummy_001 R S_cls),
                                (nb059_alpha_dummy_003 R S_cls a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
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
                              ((nb059_alpha_dummy_000 R S_cls), a),
                              ((nb059_alpha_dummy_002 R S_cls),
                                (nb059_alpha_dummy_004 R S_cls a)),
                              ((nb059_alpha_dummy_001 R S_cls),
                                (nb059_alpha_dummy_003 R S_cls a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb059_split_alpha_0008 (R : Class) (S_cls : Class) (a : Var) :
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
noncomputable def nb059_split_alpha_0009 (R : Class) (S_cls : Class) (a : Var) :
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
                                  ((nb059_alpha_dummy_000 R S_cls), a),
                                  ((nb059_alpha_dummy_002 R S_cls),
                                    (nb059_alpha_dummy_004 R S_cls a)),
                                  ((nb059_alpha_dummy_001 R S_cls),
                                    (nb059_alpha_dummy_003 R S_cls a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb059_split_alpha_0008 R S_cls a))))))))
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
                      ((nb059_alpha_dummy_000 R S_cls), a), ((nb059_alpha_dummy_002 R S_cls),
                        (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls),
                        (nb059_alpha_dummy_003 R S_cls a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb059_split_alpha_0010 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
        ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
        ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_047 R S_cls))
          (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb059_alpha_dummy_047 R S_cls))
            (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_013 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059_alpha_dummy_048 R a))
          (Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb059_alpha_dummy_048 R a))
            (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                    (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0042 R S_cls) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0043 R a) 0))
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb059_support_mem_0039 R S_cls) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0041 R a) 0))
                        (TAlphaVar.there (freshVar_injective
                            ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv)
                            (by decide))
                          (freshVar_injective ((R).fv ∪ ((Class.cv a)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
                      ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
                      ((Class.cv (nb059_alpha_dummy_015 R a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb059_split_alpha_0009 R S_cls a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                    (nb059_split_alpha_0009 R S_cls a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
                          ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
                          ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
                          ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
                          ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
                          ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                          ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                          ((nb059_alpha_dummy_000 R S_cls), a),
                          ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
                          ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 1))
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0038 R S_cls) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0040 R a) 0))
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb059_support_mem_0042 R S_cls) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0043 R a) 0))
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0039 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0041 R a) 0))
                          (TAlphaVar.there (freshVar_injective
                              ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv)
                              (by decide))
                            (freshVar_injective ((R).fv ∪ ((Class.cv a)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
                        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
                        ((Class.cv (nb059_alpha_dummy_015 R a))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb059_split_alpha_0009 R S_cls a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb059_split_alpha_0009 R S_cls a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb059_alpha_dummy_049 R S_cls), (nb059_alpha_dummy_050 R a)),
                            ((nb059_alpha_dummy_018 R S_cls), (nb059_alpha_dummy_020 R a)),
                            ((nb059_alpha_dummy_017 R S_cls), (nb059_alpha_dummy_019 R a)),
                            ((nb059_alpha_dummy_047 R S_cls), (nb059_alpha_dummy_048 R a)),
                            ((nb059_alpha_dummy_021 R S_cls), (nb059_alpha_dummy_022 R a)),
                            ((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                            ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                            ((nb059_alpha_dummy_000 R S_cls), a),
                            ((nb059_alpha_dummy_002 R S_cls),
                              (nb059_alpha_dummy_004 R S_cls a)),
                            ((nb059_alpha_dummy_001 R S_cls),
                              (nb059_alpha_dummy_003 R S_cls a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

theorem nb059_compact_envfresh_0017 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TEnvFresh
      [((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (R).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb059_alpha_dummy_014 R S_cls) (nb059_alpha_dummy_016 R a)
      (nb059_wpp_notmem_0148 R S_cls) (nb059_wpp_notmem_0149 R a)
      (TEnvFresh.consFresh (nb059_alpha_dummy_013 R S_cls) (nb059_alpha_dummy_015 R a)
        (nb059_wpp_notmem_0150 R S_cls) (nb059_wpp_notmem_0151 R a)
        (TEnvFresh.consFresh (nb059_alpha_dummy_000 R S_cls) a
          (nb059_wpp_notmem_0156 R S_cls) (nb059_wpp_notmem_0157 R a dv_R_a)
          (TEnvFresh.consFresh (nb059_alpha_dummy_002 R S_cls)
            (nb059_alpha_dummy_004 R S_cls a) (nb059_wpp_notmem_0158 R S_cls)
            (nb059_wpp_notmem_0159 R S_cls a dv_R_a)
            (TEnvFresh.consFresh (nb059_alpha_dummy_001 R S_cls)
              (nb059_alpha_dummy_003 R S_cls a) (nb059_wpp_notmem_0160 R S_cls)
              (nb059_wpp_notmem_0161 R S_cls a dv_R_a) (TEnvFresh.nil (R).fv))))))

@[expose]
noncomputable def nb059_wpp_refl_0017 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) :
    TReflOn
      [((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
        ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
        ((nb059_alpha_dummy_000 R S_cls), a),
        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
      (R).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0017 R S_cls a dv_R_a)

@[expose]
noncomputable def nominal_df_clos1 (R : Class) (S_cls : Class) (a : Var)
    (dv_R_a : a ∉ R.fv) (dv_S_a : a ∉ S_cls.fv) :
    Nominal.NPrf
      (.classEq (syn_cclos1 S_cls R) (syn_cint (.cab a
            (syn_wa (syn_wss S_cls (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_reflOn
                                      [((nb059_alpha_dummy_007 R S_cls),
        (nb059_alpha_dummy_008 S_cls a)), ((nb059_alpha_dummy_005 R S_cls),
        (nb059_alpha_dummy_006 S_cls a)), ((nb059_alpha_dummy_000 R S_cls), a),
                                        ((nb059_alpha_dummy_002 R S_cls),
        (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls),
        (nb059_alpha_dummy_003 R S_cls a))] S_cls (nb059_wpp_refl_0000 R S_cls a dv_S_a)))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb059_support_mem_0002 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0003 S_cls a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0000 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0001 S_cls a) 0)) (TAlphaVar.here _ _ _)))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_reflOn
                                      [((nb059_alpha_dummy_007 R S_cls),
        (nb059_alpha_dummy_008 S_cls a)), ((nb059_alpha_dummy_005 R S_cls),
        (nb059_alpha_dummy_006 S_cls a)), ((nb059_alpha_dummy_000 R S_cls), a),
                                        ((nb059_alpha_dummy_002 R S_cls),
        (nb059_alpha_dummy_004 R S_cls a)), ((nb059_alpha_dummy_001 R S_cls),
        (nb059_alpha_dummy_003 R S_cls a))] S_cls (nb059_wpp_refl_0000 R S_cls a dv_S_a)))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb059_support_mem_0002 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0003 S_cls a) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0000 R S_cls) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb059_support_mem_0001 S_cls a) 0)) (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaClass.refl_of_reflOn [((nb059_alpha_dummy_000 R S_cls), a),
                        ((nb059_alpha_dummy_002 R S_cls), (nb059_alpha_dummy_004 R S_cls a)),
                        ((nb059_alpha_dummy_001 R S_cls), (nb059_alpha_dummy_003 R S_cls a))]
                      S_cls (nb059_wpp_refl_0001 R S_cls a dv_S_a))) (TAlphaWff.classEq
                    (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.neg (nb059_split_alpha_0005 R S_cls a dv_R_a))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb059_support_mem_0008 R S_cls) 1))
                                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0009 R a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0008 R S_cls) 0))
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb059_support_mem_0009 R a) 0))
                                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb059_split_alpha_0007 R S_cls a))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb059_split_alpha_0007 R S_cls a))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb059_split_alpha_0010 R S_cls a)))))))) (TAlphaClass.refl_of_reflOn
                              [((nb059_alpha_dummy_014 R S_cls), (nb059_alpha_dummy_016 R a)),
                                ((nb059_alpha_dummy_013 R S_cls), (nb059_alpha_dummy_015 R a)),
                                ((nb059_alpha_dummy_000 R S_cls), a),
                                ((nb059_alpha_dummy_002 R S_cls),
                                  (nb059_alpha_dummy_004 R S_cls a)),
                                ((nb059_alpha_dummy_001 R S_cls),
                                  (nb059_alpha_dummy_003 R S_cls a))]
                              R (nb059_wpp_refl_0017 R S_cls a dv_R_a))))))))))
            (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb059_alpha_dummy_000 R S_cls)
                      (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
                        (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
                          (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) (by decide))
                (freshVar_injective (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
                        (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
