/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.FiniteTypeAlpha


/-! NF weak partition development: NominalAlphaRepairedBase001028Tfin. -/


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

namespace FiniteTypeAlpha

@[expose]
noncomputable def split_alpha_0000 (n : Var) (M : Class) (a : Var) (__dv_M_a : a ∉ M.fv)
    (__dv_M_n : n ∉ M.fv) (__dv_a_n : a ≠ n) :
    TAlphaWff
      [(alpha_dummy_020, alpha_dummy_020), (alpha_dummy_019, alpha_dummy_019),
        (alpha_dummy_018, alpha_dummy_018), (alpha_dummy_014, alpha_dummy_014),
        (alpha_dummy_006, alpha_dummy_006), (alpha_dummy_016, alpha_dummy_016),
        (alpha_dummy_015, alpha_dummy_015), ((alpha_dummy_001 M), n),
        ((alpha_dummy_008 M), (alpha_dummy_009 n M a)),
        ((alpha_dummy_011 M), (alpha_dummy_013 n M a)),
        ((alpha_dummy_010 M), (alpha_dummy_012 n M a)),
        ((alpha_dummy_002 M), (alpha_dummy_003 n M a))]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_018)
            (syn_cun (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_018)
            (syn_cun (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))))) :=
  by
  have fresh_003_local := (fresh_003 M)
  have fresh_004_local := (fresh_004 M)
  have fresh_006_local := (fresh_006 n M a)
  have fresh_007_local := (fresh_007 n M a)
  have fresh_025_local := (fresh_025 M)
  have fresh_026_local := (fresh_026 n M a)
  have fresh_039_local := (fresh_039 M)
  have fresh_040_local := (fresh_040 M)
  have fresh_042_local := (fresh_042 M)
  have fresh_043_local := (fresh_043 n M a)
  exact
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0001 (n : Var) (M : Class) (a : Var) (__dv_M_a : a ∉ M.fv)
    (__dv_M_n : n ∉ M.fv) (__dv_a_n : a ≠ n) :
    TAlphaWff
      [((alpha_dummy_027 M), (alpha_dummy_028 a)), ((alpha_dummy_000 M), a),
        ((alpha_dummy_001 M), n), ((alpha_dummy_008 M), (alpha_dummy_009 n M a)),
        ((alpha_dummy_011 M), (alpha_dummy_013 n M a)),
        ((alpha_dummy_010 M), (alpha_dummy_012 n M a)),
        ((alpha_dummy_002 M), (alpha_dummy_003 n M a))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_027 M))
          (syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_027 M))
            (syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c)))))
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_028 a))
          (syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv (alpha_dummy_028 a))
            (syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))))) :=
  by
  have fresh_003_local := (fresh_003 M)
  have fresh_004_local := (fresh_004 M)
  have fresh_006_local := (fresh_006 n M a)
  have fresh_007_local := (fresh_007 n M a)
  have fresh_025_local := (fresh_025 M)
  have fresh_026_local := (fresh_026 n M a)
  have fresh_039_local := (fresh_039 M)
  have fresh_040_local := (fresh_040 M)
  have fresh_042_local := (fresh_042 M)
  have fresh_043_local := (fresh_043 n M a)
  exact
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0010 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0011 a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0022 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0023 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0020 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0021 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0018 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0019 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0016 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0017 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 a) 0)) (TAlphaVar.here _ _ _))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0010 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0011 a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0022 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0023 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0020 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0021 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0018 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0019 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0016 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0017 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 a) 0)) (TAlphaVar.here _ _ _)))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0010 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0011 a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0022 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0023 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0020 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0021 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0018 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0019 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0016 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0017 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 a) 0)) (TAlphaVar.here _ _ _))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0012 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0013 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0010 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0011 a) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0022 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0023 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0020 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0021 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0018 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0019 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0016 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0017 a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0014 M) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (support_mem_0015 a) 0)) (TAlphaVar.here _ _ _)))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (TAlphaVar.here _ _ _)))))))))))))))

@[expose]
noncomputable def split_alpha_0002 (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    TAlphaWff
      [((alpha_dummy_001 M), n), ((alpha_dummy_008 M), (alpha_dummy_009 n M a)),
        ((alpha_dummy_011 M), (alpha_dummy_013 n M a)),
        ((alpha_dummy_010 M), (alpha_dummy_012 n M a)),
        ((alpha_dummy_002 M), (alpha_dummy_003 n M a))]
      (Wff.imp (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc)) (Wff.neg
          (syn_wrex (alpha_dummy_000 M) M
            (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
              (Class.cv (alpha_dummy_001 M))))))
      (Wff.imp (Wff.classMem (Class.cv n) (syn_cnnc))
        (Wff.neg (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n))))) :=
  by
  have fresh_003_local := (fresh_003 M)
  have fresh_004_local := (fresh_004 M)
  have fresh_006_local := (fresh_006 n M a)
  have fresh_007_local := (fresh_007 n M a)
  have fresh_025_local := (fresh_025 M)
  have fresh_026_local := (fresh_026 n M a)
  have fresh_039_local := (fresh_039 M)
  have fresh_040_local := (fresh_040 M)
  have fresh_042_local := (fresh_042 M)
  have fresh_043_local := (fresh_043 n M a)
  exact
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed _ _ fv_syn_cnnc)) (TAlphaWff.neg (TAlphaWff.ex
          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_fv_fresh _ _ (allVariablesFresh n M a dv_M_a dv_M_n)))
            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.neg (split_alpha_0001 n M a dv_M_a dv_M_n dv_a_n))))
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((M).fv) (by decide))
                  (Ne.symm dv_a_n) (TAlphaVar.here _ _ _))))))))

@[expose]
noncomputable def split_alpha_0003 (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    TAlphaWff [((alpha_dummy_002 M), (alpha_dummy_003 n M a))]
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (alpha_dummy_002 M)) (syn_c0))
            (Wff.classEq M (syn_c0)))) (syn_wa (Wff.classMem (Class.cv (alpha_dummy_002 M))
            (syn_cio (alpha_dummy_001 M)
              (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
                (syn_wrex (alpha_dummy_000 M) M
                  (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                    (Class.cv (alpha_dummy_001 M))))))) (Wff.neg (Wff.classEq M (syn_c0)))))
      (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (alpha_dummy_003 n M a)) (syn_c0))
            (Wff.classEq M (syn_c0)))) (syn_wa (Wff.classMem (Class.cv (alpha_dummy_003 n M a))
            (syn_cio n (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
                (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n))))))
          (Wff.neg (Wff.classEq M (syn_c0))))) :=
  by
  have fresh_003_local := (fresh_003 M)
  have fresh_004_local := (fresh_004 M)
  have fresh_006_local := (fresh_006 n M a)
  have fresh_007_local := (fresh_007 n M a)
  have fresh_025_local := (fresh_025 M)
  have fresh_026_local := (fresh_026 n M a)
  have fresh_039_local := (fresh_039 M)
  have fresh_040_local := (fresh_040 M)
  have fresh_042_local := (fresh_042 M)
  have fresh_043_local := (fresh_043 n M a)
  exact
    (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                (TAlphaVar.here _ _ _))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                (TAlphaVar.here _ _ _))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq
            (TAlphaClass.refl_of_fv_fresh _ _ (outerVariablesFresh n M a)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                (TAlphaVar.here _ _ _))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                (TAlphaVar.here _ _ _))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                      (((Class.cab (alpha_dummy_008 M) (Wff.classEq
                            (Class.cab (alpha_dummy_001 M) (syn_wa
                                (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
                                (syn_wrex (alpha_dummy_000 M) M
                                  (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                                    (Class.cv (alpha_dummy_001 M))))))
                            (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv) (by decide))
                    (freshVar_injective (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq
                            (Class.cab n (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
                                (syn_wrex a M
                                  (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
                            (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv) (by decide))
                    (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab
                        (TAlphaWff.neg (split_alpha_0002 n M a dv_M_a dv_M_n dv_a_n)))
                      (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 M) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 n M a) 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg
          (TAlphaWff.classEq (TAlphaClass.refl_of_fv_fresh _ _ (outerVariablesFresh n M a))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                (TAlphaVar.here _ _ _))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                (TAlphaVar.here _ _ _))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                        (TAlphaVar.here _ _ _)))))))))))))))))))

end FiniteTypeAlpha

@[expose]
noncomputable def nominal_df_tfin (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    Nominal.NPrf
      (.classEq (syn_ctfin M) (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n
            (syn_wa (.classMem (.cv n) (syn_cnnc))
              (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (FiniteTypeAlpha.split_alpha_0003 n M a dv_M_a dv_M_n dv_a_n))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
