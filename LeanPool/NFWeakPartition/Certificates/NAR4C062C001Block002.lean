/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C062C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C062C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0000`. -/
@[expose]
noncomputable def nb062SplitAlpha0000 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy022), (nb062AlphaDummy025 r a)),
        ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
        ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)),
        ((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
        ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
        ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
        ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
        ((nb062AlphaDummy012), (nb062AlphaDummy013 r a)),
        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb062AlphaDummy020))
            (synCun (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy023 r a))
            (synCun (Class.cv (nb062AlphaDummy024 r a))
              (Class.cv (nb062AlphaDummy025 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb062AlphaDummy022), (nb062AlphaDummy025 r a)),
          ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
          ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)),
          ((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
          ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
          ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
          ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
          ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
          ((nb062AlphaDummy012), (nb062AlphaDummy013 r a)),
          ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
          ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
          ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0001`. -/
@[expose]
noncomputable def nb062SplitAlpha0001 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
        ((nb062AlphaDummy012), (nb062AlphaDummy013 r a)),
        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy007))
          (Class.cv (nb062AlphaDummy001))) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy006))
            (synCphi (Class.cv (nb062AlphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy009 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy008 r a))
            (synCphi (Class.cv (nb062AlphaDummy009 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb062AlphaDummy001))).fv ∪
                ((Class.cv (nb062AlphaDummy000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb062AlphaDummy007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb062AlphaDummy009 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb062AlphaDummy022),
        (nb062AlphaDummy025 r a)), ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
        ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)), ((nb062AlphaDummy018),
        (nb062AlphaDummy019 r a)), ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
        ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)), ((nb062AlphaDummy007),
        (nb062AlphaDummy009 r a)), ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
        ((nb062AlphaDummy012), (nb062AlphaDummy013 r a)), ((nb062AlphaDummy010),
        (nb062AlphaDummy011 r a)), ((nb062AlphaDummy000), a),
        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb062SplitAlpha0000 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                              ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                              ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                              ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                              ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                              ((nb062AlphaDummy012), (nb062AlphaDummy013 r a)),
                              ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                              ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                              ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                              ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                              ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                              ((nb062AlphaDummy012), (nb062AlphaDummy013 r a)),
                              ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0002`. -/
@[expose]
noncomputable def nb062SplitAlpha0002 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy022), (nb062AlphaDummy025 r a)),
        ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
        ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)),
        ((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
        ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
        ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
        ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
        ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
        ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
        ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb062AlphaDummy020))
            (synCun (Class.cv (nb062AlphaDummy021)) (Class.cv (nb062AlphaDummy022))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb062AlphaDummy024 r a))
            (Class.cv (nb062AlphaDummy025 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy023 r a))
            (synCun (Class.cv (nb062AlphaDummy024 r a))
              (Class.cv (nb062AlphaDummy025 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb062AlphaDummy022), (nb062AlphaDummy025 r a)),
          ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
          ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)),
          ((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
          ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
          ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
          ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
          ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
          ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
          ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
          ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
          ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
          ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
          ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy014))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy016 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0003`. -/
@[expose]
noncomputable def nb062SplitAlpha0003 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
        ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
        ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
        ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy040))
          (synCphi (Class.cv (nb062AlphaDummy007)))) (Wff.neg
          (Wff.classMem (Class.cv (nb062AlphaDummy040))
            (synCphi (Class.cv (nb062AlphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy041 r a))
          (synCphi (Class.cv (nb062AlphaDummy009 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb062AlphaDummy041 r a))
            (synCphi (Class.cv (nb062AlphaDummy009 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb062AlphaDummy007))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb062AlphaDummy009 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb062AlphaDummy022),
        (nb062AlphaDummy025 r a)), ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
                                        ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)),
                                        ((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                                        ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                                        ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                                        ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
                                        ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
                                        ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                                        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                                        ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                                        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                                        ((nb062AlphaDummy000), a),
                                        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb062SplitAlpha0002 x y r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                            ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                            ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                            ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
                            ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
                            ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                            ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                            ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                            ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                            ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                            ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                            ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                            ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                            ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
                            ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
                            ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                            ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                            ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                            ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                            ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                            ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb062AlphaDummy007))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb062AlphaDummy009 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb062AlphaDummy022),
        (nb062AlphaDummy025 r a)), ((nb062AlphaDummy021), (nb062AlphaDummy024 r a)),
        ((nb062AlphaDummy020), (nb062AlphaDummy023 r a)), ((nb062AlphaDummy018),
        (nb062AlphaDummy019 r a)), ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
        ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)), ((nb062AlphaDummy040),
        (nb062AlphaDummy041 r a)), ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
        ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)), ((nb062AlphaDummy006),
        (nb062AlphaDummy008 r a)), ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)), ((nb062AlphaDummy000), a),
        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb062SplitAlpha0002 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                              ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                              ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                              ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
                              ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
                              ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                              ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                              ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                              ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy018), (nb062AlphaDummy019 r a)),
                              ((nb062AlphaDummy014), (nb062AlphaDummy016 r a)),
                              ((nb062AlphaDummy015), (nb062AlphaDummy017 r a)),
                              ((nb062AlphaDummy040), (nb062AlphaDummy041 r a)),
                              ((nb062AlphaDummy038), (nb062AlphaDummy039 r a)),
                              ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                              ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                              ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                              ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb062_pair_occurrence`. -/
@[expose]
noncomputable def nb062PairOccurrence (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaClass
      [((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Class.cv (nb062AlphaDummy004)) (Class.cv (nb062AlphaDummy005 x y r a)) :=
  by
  have freshness0 : (nb062AlphaDummy004) ≠ (nb062AlphaDummy000) :=
    by
    unfold nb062AlphaDummy004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0002) 0)))
  have freshness1 : (nb062AlphaDummy005 x y r a) ≠ a :=
    by
    unfold nb062AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0003 x y r a) 0)))
  have freshness2 : (nb062AlphaDummy004) ≠ (nb062AlphaDummy001) :=
    by
    unfold nb062AlphaDummy004
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0000) 0)))
  have freshness3 : (nb062AlphaDummy005 x y r a) ≠ r :=
    by
    unfold nb062AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0001 x y r a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0004`. -/
@[expose]
noncomputable def nb062SplitAlpha0004 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.classEq (Class.cv (nb062AlphaDummy004))
        (synCop (Class.cv (nb062AlphaDummy001)) (Class.cv (nb062AlphaDummy000))))
      (Wff.classEq (Class.cv (nb062AlphaDummy005 x y r a))
        (synCop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (nb062PairOccurrence x y r a) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb062SplitAlpha0001 x y r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb062SplitAlpha0001 x y r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy001))).fv ∪
                                    ((Class.cv (nb062AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb062SplitAlpha0003 x y r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb062AlphaDummy038),
        (nb062AlphaDummy039 r a)), ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                                        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                                        ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                                        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                                        ((nb062AlphaDummy000), a),
                                        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy001))).fv ∪
                                    ((Class.cv (nb062AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb062SplitAlpha0003 x y r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb062AlphaDummy038),
        (nb062AlphaDummy039 r a)), ((nb062AlphaDummy007), (nb062AlphaDummy009 r a)),
                                        ((nb062AlphaDummy006), (nb062AlphaDummy008 r a)),
                                        ((nb062AlphaDummy036), (nb062AlphaDummy037 r a)),
                                        ((nb062AlphaDummy010), (nb062AlphaDummy011 r a)),
                                        ((nb062AlphaDummy000), a),
                                        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0005`. -/
@[expose]
noncomputable def nb062SplitAlpha0005 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy058), (nb062AlphaDummy061 x y)),
        ((nb062AlphaDummy057), (nb062AlphaDummy060 x y)),
        ((nb062AlphaDummy056), (nb062AlphaDummy059 x y)),
        ((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
        ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
        ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
        ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
        ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
        ((nb062AlphaDummy048), (nb062AlphaDummy049 x y)),
        ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb062AlphaDummy056))
            (synCun (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy059 x y))
            (synCun (Class.cv (nb062AlphaDummy060 x y))
              (Class.cv (nb062AlphaDummy061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb062AlphaDummy058), (nb062AlphaDummy061 x y)),
          ((nb062AlphaDummy057), (nb062AlphaDummy060 x y)),
          ((nb062AlphaDummy056), (nb062AlphaDummy059 x y)),
          ((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
          ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
          ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
          ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
          ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
          ((nb062AlphaDummy048), (nb062AlphaDummy049 x y)),
          ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
          ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
          ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
          ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0006`. -/
@[expose]
noncomputable def nb062SplitAlpha0006 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
        ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
        ((nb062AlphaDummy048), (nb062AlphaDummy049 x y)),
        ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy043))
          (Class.cv (nb062AlphaDummy002))) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy042))
            (synCphi (Class.cv (nb062AlphaDummy043))))))
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy045 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
            (synCphi (Class.cv (nb062AlphaDummy045 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0044 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0047 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0045 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_x_y (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb062AlphaDummy002))).fv ∪
                ((Class.cv (nb062AlphaDummy003))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0049 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0049 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb062AlphaDummy043))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb062AlphaDummy045 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0053 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb062AlphaDummy058),
        (nb062AlphaDummy061 x y)), ((nb062AlphaDummy057), (nb062AlphaDummy060 x y)),
        ((nb062AlphaDummy056), (nb062AlphaDummy059 x y)), ((nb062AlphaDummy054),
        (nb062AlphaDummy055 x y)), ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
        ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)), ((nb062AlphaDummy043),
        (nb062AlphaDummy045 x y)), ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
        ((nb062AlphaDummy048), (nb062AlphaDummy049 x y)), ((nb062AlphaDummy046),
        (nb062AlphaDummy047 x y)), ((nb062AlphaDummy003), y),
        ((nb062AlphaDummy002), x), ((nb062AlphaDummy000), a),
        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb062SplitAlpha0005 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
                              ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
                              ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
                              ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                              ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                              ((nb062AlphaDummy048), (nb062AlphaDummy049 x y)),
                              ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                              ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
                              ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
                              ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
                              ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                              ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                              ((nb062AlphaDummy048), (nb062AlphaDummy049 x y)),
                              ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                              ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0007`. -/
@[expose]
noncomputable def nb062SplitAlpha0007 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy058), (nb062AlphaDummy061 x y)),
        ((nb062AlphaDummy057), (nb062AlphaDummy060 x y)),
        ((nb062AlphaDummy056), (nb062AlphaDummy059 x y)),
        ((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
        ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
        ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
        ((nb062AlphaDummy076), (nb062AlphaDummy077 x y)),
        ((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
        ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
        ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
        ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
        ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb062AlphaDummy056))
            (synCun (Class.cv (nb062AlphaDummy057)) (Class.cv (nb062AlphaDummy058))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb062AlphaDummy060 x y))
            (Class.cv (nb062AlphaDummy061 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy059 x y))
            (synCun (Class.cv (nb062AlphaDummy060 x y))
              (Class.cv (nb062AlphaDummy061 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb062AlphaDummy058), (nb062AlphaDummy061 x y)),
          ((nb062AlphaDummy057), (nb062AlphaDummy060 x y)),
          ((nb062AlphaDummy056), (nb062AlphaDummy059 x y)),
          ((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
          ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
          ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
          ((nb062AlphaDummy076), (nb062AlphaDummy077 x y)),
          ((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
          ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
          ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
          ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
          ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
          ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
          ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
          ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy050))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy052 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0008`. -/
@[expose]
noncomputable def nb062SplitAlpha0008 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
        ((nb062AlphaDummy076), (nb062AlphaDummy077 x y)),
        ((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
        ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
        ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
        ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
        ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.all (nb062AlphaDummy050) (Wff.neg (synWa
            (Wff.classMem (Class.cv (nb062AlphaDummy050)) (Class.cv (nb062AlphaDummy043)))
            (Wff.classEq (Class.cv (nb062AlphaDummy051))
              (synCif (Wff.classMem (Class.cv (nb062AlphaDummy050)) (synCnnc))
                (synCplc (Class.cv (nb062AlphaDummy050)) (synC1c))
                (Class.cv (nb062AlphaDummy050)))))))
      (Wff.all (nb062AlphaDummy052 x y) (Wff.neg (synWa
            (Wff.classMem (Class.cv (nb062AlphaDummy052 x y))
              (Class.cv (nb062AlphaDummy045 x y)))
            (Wff.classEq (Class.cv (nb062AlphaDummy053 x y))
              (synCif (Wff.classMem (Class.cv (nb062AlphaDummy052 x y)) (synCnnc))
                (synCplc (Class.cv (nb062AlphaDummy052 x y)) (synC1c))
                (Class.cv (nb062AlphaDummy052 x y))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0048) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0049 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0048) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0049 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0078) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0079 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0076) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0077 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb062AlphaDummy043))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy045 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0052) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0053 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0052) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0053 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0050) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb062AlphaDummy058), (nb062AlphaDummy061 x y)),
                                    ((nb062AlphaDummy057), (nb062AlphaDummy060 x y)),
                                    ((nb062AlphaDummy056), (nb062AlphaDummy059 x y)),
                                    ((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
                                    ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
                                    ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
                                    ((nb062AlphaDummy076), (nb062AlphaDummy077 x y)),
                                    ((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
                                    ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                                    ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                                    ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
                                    ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                                    ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                                    ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                                    ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb062SplitAlpha0007 x y r a))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
                        ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
                        ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
                        ((nb062AlphaDummy076), (nb062AlphaDummy077 x y)),
                        ((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
                        ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                        ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                        ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
                        ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0051 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb062AlphaDummy054), (nb062AlphaDummy055 x y)),
                        ((nb062AlphaDummy050), (nb062AlphaDummy052 x y)),
                        ((nb062AlphaDummy051), (nb062AlphaDummy053 x y)),
                        ((nb062AlphaDummy076), (nb062AlphaDummy077 x y)),
                        ((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
                        ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                        ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                        ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
                        ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0009`. -/
@[expose]
noncomputable def nb062SplitAlpha0009 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy046)) (synCcompl
            (Class.cab (nb062AlphaDummy042)
              (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy002))
                (Wff.classEq (Class.cv (nb062AlphaDummy042))
                  (synCphi (Class.cv (nb062AlphaDummy043)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb062AlphaDummy046)) (synCcompl
              (Class.cab (nb062AlphaDummy042)
                (synWrex (nb062AlphaDummy043) (Class.cv (nb062AlphaDummy003))
                  (Wff.classEq (Class.cv (nb062AlphaDummy042))
                    (synCun (synCphi (Class.cv (nb062AlphaDummy043)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy047 x y)) (synCcompl
            (Class.cab (nb062AlphaDummy044 x y)
              (synWrex (nb062AlphaDummy045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                  (synCphi (Class.cv (nb062AlphaDummy045 x y)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb062AlphaDummy047 x y)) (synCcompl
              (Class.cab (nb062AlphaDummy044 x y)
                (synWrex (nb062AlphaDummy045 x y) (Class.cv y)
                  (Wff.classEq (Class.cv (nb062AlphaDummy044 x y))
                    (synCun (synCphi (Class.cv (nb062AlphaDummy045 x y)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb062SplitAlpha0006 x y r a dv_x_y)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb062SplitAlpha0006 x y r a dv_x_y)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0074) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0075 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0071) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0073 x y) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb062AlphaDummy002))).fv ∪
                                ((Class.cv (nb062AlphaDummy003))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb062SplitAlpha0008 x y r a)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb062SplitAlpha0008 x y r a))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
                                    ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                                    ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                                    ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
                                    ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                                    ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                                    ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                                    ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0072 x y) 0))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0074) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0075 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0071) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0073 x y) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb062AlphaDummy002))).fv ∪
                                ((Class.cv (nb062AlphaDummy003))).fv) (by decide))
                            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb062SplitAlpha0008 x y r a)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (nb062SplitAlpha0008 x y r a))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb062AlphaDummy074), (nb062AlphaDummy075 x y)),
                                    ((nb062AlphaDummy043), (nb062AlphaDummy045 x y)),
                                    ((nb062AlphaDummy042), (nb062AlphaDummy044 x y)),
                                    ((nb062AlphaDummy072), (nb062AlphaDummy073 x y)),
                                    ((nb062AlphaDummy046), (nb062AlphaDummy047 x y)),
                                    ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                                    ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                                    ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0010`. -/
@[expose]
noncomputable def nb062SplitAlpha0010 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy094), (nb062AlphaDummy097 x y)),
        ((nb062AlphaDummy093), (nb062AlphaDummy096 x y)),
        ((nb062AlphaDummy092), (nb062AlphaDummy095 x y)),
        ((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
        ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
        ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
        ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
        ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
        ((nb062AlphaDummy084), (nb062AlphaDummy085 x y)),
        ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb062AlphaDummy092))
            (synCun (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy095 x y))
            (synCun (Class.cv (nb062AlphaDummy096 x y))
              (Class.cv (nb062AlphaDummy097 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb062AlphaDummy094), (nb062AlphaDummy097 x y)),
          ((nb062AlphaDummy093), (nb062AlphaDummy096 x y)),
          ((nb062AlphaDummy092), (nb062AlphaDummy095 x y)),
          ((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
          ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
          ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
          ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
          ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
          ((nb062AlphaDummy084), (nb062AlphaDummy085 x y)),
          ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
          ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
          ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
          ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C062C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0011`. -/
@[expose]
noncomputable def nb062SplitAlpha0011 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
        ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
        ((nb062AlphaDummy084), (nb062AlphaDummy085 x y)),
        ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy079))
          (Class.cv (nb062AlphaDummy003))) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy078))
            (synCphi (Class.cv (nb062AlphaDummy079))))))
      (Wff.imp (Wff.classMem (Class.cv (nb062AlphaDummy081 x y)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
            (synCphi (Class.cv (nb062AlphaDummy081 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0080) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0082 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0084) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0085 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0081) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0083 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb062AlphaDummy003))).fv ∪
                ((Class.cv (nb062AlphaDummy002))).fv) (by decide))
            (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0086) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0087 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0086) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0087 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb062AlphaDummy079))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb062AlphaDummy081 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0090) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb062_support_mem_0091 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0090) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0091 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0088) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb062_support_mem_0089 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb062AlphaDummy094),
        (nb062AlphaDummy097 x y)), ((nb062AlphaDummy093), (nb062AlphaDummy096 x y)),
        ((nb062AlphaDummy092), (nb062AlphaDummy095 x y)), ((nb062AlphaDummy090),
        (nb062AlphaDummy091 x y)), ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
        ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)), ((nb062AlphaDummy079),
        (nb062AlphaDummy081 x y)), ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
        ((nb062AlphaDummy084), (nb062AlphaDummy085 x y)), ((nb062AlphaDummy082),
        (nb062AlphaDummy083 x y)), ((nb062AlphaDummy003), y),
        ((nb062AlphaDummy002), x), ((nb062AlphaDummy000), a),
        ((nb062AlphaDummy001), r), ((nb062AlphaDummy004),
        (nb062AlphaDummy005 x y r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb062SplitAlpha0010 x y r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
                              ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
                              ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
                              ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                              ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                              ((nb062AlphaDummy084), (nb062AlphaDummy085 x y)),
                              ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                              ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0088) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
                              ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
                              ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
                              ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                              ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                              ((nb062AlphaDummy084), (nb062AlphaDummy085 x y)),
                              ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                              ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                              ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                              ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0012`. -/
@[expose]
noncomputable def nb062SplitAlpha0012 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy094), (nb062AlphaDummy097 x y)),
        ((nb062AlphaDummy093), (nb062AlphaDummy096 x y)),
        ((nb062AlphaDummy092), (nb062AlphaDummy095 x y)),
        ((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
        ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
        ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
        ((nb062AlphaDummy112), (nb062AlphaDummy113 x y)),
        ((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
        ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
        ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
        ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
        ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb062AlphaDummy092))
            (synCun (Class.cv (nb062AlphaDummy093)) (Class.cv (nb062AlphaDummy094))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb062AlphaDummy096 x y))
            (Class.cv (nb062AlphaDummy097 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb062AlphaDummy095 x y))
            (synCun (Class.cv (nb062AlphaDummy096 x y))
              (Class.cv (nb062AlphaDummy097 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0095 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0093 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0099 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0097 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb062AlphaDummy094), (nb062AlphaDummy097 x y)),
          ((nb062AlphaDummy093), (nb062AlphaDummy096 x y)),
          ((nb062AlphaDummy092), (nb062AlphaDummy095 x y)),
          ((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
          ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
          ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
          ((nb062AlphaDummy112), (nb062AlphaDummy113 x y)),
          ((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
          ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
          ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
          ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
          ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
          ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
          ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
          ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0103 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0101 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy086))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb062AlphaDummy088 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0107 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0105 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0013`. -/
@[expose]
noncomputable def nb062SplitAlpha0013 (x : Var) (y : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
        ((nb062AlphaDummy112), (nb062AlphaDummy113 x y)),
        ((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
        ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
        ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
        ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
        ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.all (nb062AlphaDummy086) (Wff.neg (synWa
            (Wff.classMem (Class.cv (nb062AlphaDummy086)) (Class.cv (nb062AlphaDummy079)))
            (Wff.classEq (Class.cv (nb062AlphaDummy087))
              (synCif (Wff.classMem (Class.cv (nb062AlphaDummy086)) (synCnnc))
                (synCplc (Class.cv (nb062AlphaDummy086)) (synC1c))
                (Class.cv (nb062AlphaDummy086)))))))
      (Wff.all (nb062AlphaDummy088 x y) (Wff.neg (synWa
            (Wff.classMem (Class.cv (nb062AlphaDummy088 x y))
              (Class.cv (nb062AlphaDummy081 x y)))
            (Wff.classEq (Class.cv (nb062AlphaDummy089 x y))
              (synCif (Wff.classMem (Class.cv (nb062AlphaDummy088 x y)) (synCnnc))
                (synCplc (Class.cv (nb062AlphaDummy088 x y)) (synC1c))
                (Class.cv (nb062AlphaDummy088 x y))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0086) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0087 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0086) 1))
                (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0087 x y) 1)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0116) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0117 x y) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0114) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0115 x y) 0))
                    (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there
              (freshVar_injective (((Class.cv (nb062AlphaDummy079))).fv) (by decide))
              (freshVar_injective (((Class.cv (nb062AlphaDummy081 x y))).fv) (by decide))
              (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0090) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb062_support_mem_0091 x y) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0090) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb062_support_mem_0091 x y) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0088) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                                    (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb062AlphaDummy094), (nb062AlphaDummy097 x y)),
                                    ((nb062AlphaDummy093), (nb062AlphaDummy096 x y)),
                                    ((nb062AlphaDummy092), (nb062AlphaDummy095 x y)),
                                    ((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
                                    ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
                                    ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
                                    ((nb062AlphaDummy112), (nb062AlphaDummy113 x y)),
                                    ((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
                                    ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                                    ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                                    ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
                                    ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                                    ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                                    ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                                    ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                                  (synC1c) (by simp only [fv_syn_c1c])))
                              (TAlphaWff.neg (nb062SplitAlpha0012 x y r a))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0088) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
                        ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
                        ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
                        ((nb062AlphaDummy112), (nb062AlphaDummy113 x y)),
                        ((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
                        ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                        ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                        ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
                        ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                      (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0088) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                      (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                    (TAlphaClass.cv (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0088) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0089 x y) 0))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                      [((nb062AlphaDummy090), (nb062AlphaDummy091 x y)),
                        ((nb062AlphaDummy086), (nb062AlphaDummy088 x y)),
                        ((nb062AlphaDummy087), (nb062AlphaDummy089 x y)),
                        ((nb062AlphaDummy112), (nb062AlphaDummy113 x y)),
                        ((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
                        ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                        ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                        ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
                        ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                      (synCnnc) (by simp only [fv_syn_cnnc])))))))))))

/-- Checked nominal proof certificate identified upstream as `nb062_split_alpha_0014`. -/
@[expose]
noncomputable def nb062SplitAlpha0014 (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
        ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
        ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
        ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
      (Wff.classMem (Class.cv (nb062AlphaDummy082)) (synCcompl
          (Class.cab (nb062AlphaDummy078)
            (synWrex (nb062AlphaDummy079) (Class.cv (nb062AlphaDummy002))
              (Wff.classEq (Class.cv (nb062AlphaDummy078))
                (synCun (synCphi (Class.cv (nb062AlphaDummy079))) (synCsn (synC0c))))))))
      (Wff.classMem (Class.cv (nb062AlphaDummy083 x y)) (synCcompl
          (Class.cab (nb062AlphaDummy080 x y)
            (synWrex (nb062AlphaDummy081 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb062AlphaDummy080 x y))
                (synCun (synCphi (Class.cv (nb062AlphaDummy081 x y)))
                  (synCsn (synC0c)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 1))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0113 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0109) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0111 x y) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                                (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb062AlphaDummy003))).fv ∪
                            ((Class.cv (nb062AlphaDummy002))).fv) (by decide))
                        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (nb062SplitAlpha0013 x y r a))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (nb062SplitAlpha0013 x y r a))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.reflOfClosed
                              [((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
                                ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                                ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                                ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
                                ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                                ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                                ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                                ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                              (synCcompl (synCsn (synC0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 1))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 1))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0108) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0110 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0112) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0113 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0109) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb062_support_mem_0111 x y) 0))
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                                (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb062AlphaDummy003))).fv ∪
                            ((Class.cv (nb062AlphaDummy002))).fv) (by decide))
                        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv x)).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (nb062SplitAlpha0013 x y r a))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (nb062SplitAlpha0013 x y r a))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.reflOfClosed
                              [((nb062AlphaDummy110), (nb062AlphaDummy111 x y)),
                                ((nb062AlphaDummy079), (nb062AlphaDummy081 x y)),
                                ((nb062AlphaDummy078), (nb062AlphaDummy080 x y)),
                                ((nb062AlphaDummy108), (nb062AlphaDummy109 x y)),
                                ((nb062AlphaDummy082), (nb062AlphaDummy083 x y)),
                                ((nb062AlphaDummy003), y), ((nb062AlphaDummy002), x),
                                ((nb062AlphaDummy000), a), ((nb062AlphaDummy001), r),
                                ((nb062AlphaDummy004), (nb062AlphaDummy005 x y r a))]
                              (synCcompl (synCsn (synC0c))) (by
                                simp only [fv_syn_ccompl, fv_syn_csn,
                                  fv_syn_c0c])))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_antisym`. -/
@[expose]
noncomputable def nominalDfAntisym (x : Var) (y : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCantisym) (synCopab r a (synWral x (.cv a) (synWral y (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
                (.objEq x y)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb062SplitAlpha0004 x y r a dv_a_r) (TAlphaWff.all
                (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_x
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.imp (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb062SplitAlpha0009 x y r a dv_x_y))))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    (Ne.symm dv_a_r) (TAlphaVar.here _ _ _))))))
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb062SplitAlpha0011 x y r a))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb062SplitAlpha0011 x y r a))))))))) (nb062SplitAlpha0014 x y r a dv_x_y))))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))
                        (TAlphaWff.objEq (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                            (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
