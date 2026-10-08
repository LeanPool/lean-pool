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

/-- Proof-translation construction identified upstream as `split_alpha_0000`. -/
@[expose]
noncomputable def splitAlpha0000 (n : Var) (M : Class) (a : Var) (__dv_M_a : a ∉ M.fv)
    (__dv_M_n : n ∉ M.fv) (__dv_a_n : a ≠ n) :
    TAlphaWff
      [(alphaDummy020, alphaDummy020), (alphaDummy019, alphaDummy019),
        (alphaDummy018, alphaDummy018), (alphaDummy014, alphaDummy014),
        (alphaDummy006, alphaDummy006), (alphaDummy016, alphaDummy016),
        (alphaDummy015, alphaDummy015), ((alphaDummy001 M), n),
        ((alphaDummy008 M), (alphaDummy009 n M a)),
        ((alphaDummy011 M), (alphaDummy013 n M a)),
        ((alphaDummy010 M), (alphaDummy012 n M a)),
        ((alphaDummy002 M), (alphaDummy003 n M a))]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy019) (Class.cv alphaDummy020))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy018)
            (synCun (Class.cv alphaDummy019) (Class.cv alphaDummy020)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy019) (Class.cv alphaDummy020))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy018)
            (synCun (Class.cv alphaDummy019) (Class.cv alphaDummy020))))) :=
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
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
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
              (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
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
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy014)).fv ∪ ((synC1c)).fv)
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

/-- Proof-translation construction identified upstream as `split_alpha_0001`. -/
@[expose]
noncomputable def splitAlpha0001 (n : Var) (M : Class) (a : Var) (__dv_M_a : a ∉ M.fv)
    (__dv_M_n : n ∉ M.fv) (__dv_a_n : a ≠ n) :
    TAlphaWff
      [((alphaDummy027 M), (alphaDummy028 a)), ((alphaDummy000 M), a),
        ((alphaDummy001 M), n), ((alphaDummy008 M), (alphaDummy009 n M a)),
        ((alphaDummy011 M), (alphaDummy013 n M a)),
        ((alphaDummy010 M), (alphaDummy012 n M a)),
        ((alphaDummy002 M), (alphaDummy003 n M a))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy027 M))
          (synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy027 M))
            (synCnin (synCpw (Class.cv (alphaDummy000 M))) (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy028 a))
          (synCnin (synCpw (Class.cv a)) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy028 a))
            (synCnin (synCpw (Class.cv a)) (synC1c))))) :=
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

/-- Proof-translation construction identified upstream as `split_alpha_0002`. -/
@[expose]
noncomputable def splitAlpha0002 (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    TAlphaWff
      [((alphaDummy001 M), n), ((alphaDummy008 M), (alphaDummy009 n M a)),
        ((alphaDummy011 M), (alphaDummy013 n M a)),
        ((alphaDummy010 M), (alphaDummy012 n M a)),
        ((alphaDummy002 M), (alphaDummy003 n M a))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc)) (Wff.neg
          (synWrex (alphaDummy000 M) M
            (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
              (Class.cv (alphaDummy001 M))))))
      (Wff.imp (Wff.classMem (Class.cv n) (synCnnc))
        (Wff.neg (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n))))) :=
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
        (TAlphaClass.reflOfClosed _ _ fv_syn_cnnc)) (TAlphaWff.neg (TAlphaWff.ex
          (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfFvFresh _ _ (allVariablesFresh n M a dv_M_a dv_M_n)))
            (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.neg (splitAlpha0001 n M a dv_M_a dv_M_n dv_a_n))))
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((M).fv) (by decide))
                  (Ne.symm dv_a_n) (TAlphaVar.here _ _ _))))))))

/-- Proof-translation construction identified upstream as `split_alpha_0003`. -/
@[expose]
noncomputable def splitAlpha0003 (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    TAlphaWff [((alphaDummy002 M), (alphaDummy003 n M a))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (alphaDummy002 M)) (synC0))
            (Wff.classEq M (synC0)))) (synWa (Wff.classMem (Class.cv (alphaDummy002 M))
            (synCio (alphaDummy001 M)
              (synWa (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
                (synWrex (alphaDummy000 M) M
                  (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                    (Class.cv (alphaDummy001 M))))))) (Wff.neg (Wff.classEq M (synC0)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (alphaDummy003 n M a)) (synC0))
            (Wff.classEq M (synC0)))) (synWa (Wff.classMem (Class.cv (alphaDummy003 n M a))
            (synCio n (synWa (Wff.classMem (Class.cv n) (synCnnc))
                (synWrex a M (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n))))))
          (Wff.neg (Wff.classEq M (synC0))))) :=
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
            (TAlphaClass.reflOfFvFresh _ _ (outerVariablesFresh n M a)) (TAlphaClass.cab
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
                      (((Class.cab (alphaDummy008 M) (Wff.classEq
                            (Class.cab (alphaDummy001 M) (synWa
                                (Wff.classMem (Class.cv (alphaDummy001 M)) (synCnnc))
                                (synWrex (alphaDummy000 M) M
                                  (Wff.classMem (synCpw1 (Class.cv (alphaDummy000 M)))
                                    (Class.cv (alphaDummy001 M))))))
                            (synCsn (Class.cv (alphaDummy008 M)))))).fv) (by decide))
                    (freshVar_injective (((Class.cab (alphaDummy009 n M a) (Wff.classEq
                            (Class.cab n (synWa (Wff.classMem (Class.cv n) (synCnnc))
                                (synWrex a M
                                  (Wff.classMem (synCpw1 (Class.cv a)) (Class.cv n)))))
                            (synCsn (Class.cv (alphaDummy009 n M a)))))).fv) (by decide))
                    (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab
                        (TAlphaWff.neg (splitAlpha0002 n M a dv_M_a dv_M_n dv_a_n)))
                      (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 M) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 n M a) 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg
          (TAlphaWff.classEq (TAlphaClass.reflOfFvFresh _ _ (outerVariablesFresh n M a))
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

/-- Checked nominal proof certificate identified upstream as `nominal_df_tfin`. -/
@[expose]
noncomputable def nominalDfTfin (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    Nominal.NPrf
      (.classEq (synCtfin M) (synCif (.classEq M (synC0)) (synC0) (synCio n
            (synWa (.classMem (.cv n) (synCnnc))
              (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (FiniteTypeAlpha.splitAlpha0003 n M a dv_M_a dv_M_n dv_a_n))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
