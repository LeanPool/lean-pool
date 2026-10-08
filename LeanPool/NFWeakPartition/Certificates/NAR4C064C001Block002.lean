/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C064C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C064C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0000`. -/
@[expose]
noncomputable def nb064SplitAlpha0000 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy023), (nb064AlphaDummy026 r a)),
        ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
        ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)),
        ((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
        ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
        ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
        ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
        ((nb064AlphaDummy013), (nb064AlphaDummy014 r a)),
        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
        ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb064AlphaDummy021))
            (synCun (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy024 r a))
            (synCun (Class.cv (nb064AlphaDummy025 r a))
              (Class.cv (nb064AlphaDummy026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb064AlphaDummy023), (nb064AlphaDummy026 r a)),
          ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
          ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)),
          ((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
          ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
          ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
          ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
          ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
          ((nb064AlphaDummy013), (nb064AlphaDummy014 r a)),
          ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
          ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
          ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0001`. -/
@[expose]
noncomputable def nb064SplitAlpha0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
        ((nb064AlphaDummy013), (nb064AlphaDummy014 r a)),
        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
        ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy008))
          (Class.cv (nb064AlphaDummy001))) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy007))
            (synCphi (Class.cv (nb064AlphaDummy008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy010 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy009 r a))
            (synCphi (Class.cv (nb064AlphaDummy010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb064AlphaDummy001))).fv ∪
                ((Class.cv (nb064AlphaDummy000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb064AlphaDummy008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb064AlphaDummy010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb064AlphaDummy023),
        (nb064AlphaDummy026 r a)), ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
        ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)), ((nb064AlphaDummy019),
        (nb064AlphaDummy020 r a)), ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
        ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)), ((nb064AlphaDummy008),
        (nb064AlphaDummy010 r a)), ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
        ((nb064AlphaDummy013), (nb064AlphaDummy014 r a)), ((nb064AlphaDummy011),
        (nb064AlphaDummy012 r a)), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
        (nb064AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb064SplitAlpha0000 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                              ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                              ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                              ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                              ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                              ((nb064AlphaDummy013), (nb064AlphaDummy014 r a)),
                              ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                              ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
                              ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                              ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                              ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                              ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                              ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                              ((nb064AlphaDummy013), (nb064AlphaDummy014 r a)),
                              ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                              ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
                              ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0002`. -/
@[expose]
noncomputable def nb064SplitAlpha0002 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy023), (nb064AlphaDummy026 r a)),
        ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
        ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)),
        ((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
        ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
        ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
        ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
        ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
        ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
        ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
        ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb064AlphaDummy021))
            (synCun (Class.cv (nb064AlphaDummy022)) (Class.cv (nb064AlphaDummy023))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb064AlphaDummy025 r a))
            (Class.cv (nb064AlphaDummy026 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy024 r a))
            (synCun (Class.cv (nb064AlphaDummy025 r a))
              (Class.cv (nb064AlphaDummy026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb064AlphaDummy023), (nb064AlphaDummy026 r a)),
          ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
          ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)),
          ((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
          ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
          ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
          ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
          ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
          ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
          ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
          ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
          ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
          ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
          ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C064C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0003`. -/
@[expose]
noncomputable def nb064SplitAlpha0003 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
        ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
        ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
        ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
        ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy041))
          (synCphi (Class.cv (nb064AlphaDummy008)))) (Wff.neg
          (Wff.classMem (Class.cv (nb064AlphaDummy041))
            (synCphi (Class.cv (nb064AlphaDummy008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy042 r a))
          (synCphi (Class.cv (nb064AlphaDummy010 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb064AlphaDummy042 r a))
            (synCphi (Class.cv (nb064AlphaDummy010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb064AlphaDummy008))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb064AlphaDummy010 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb064AlphaDummy023),
        (nb064AlphaDummy026 r a)), ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
                                        ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)),
                                        ((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                                        ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                                        ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                                        ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
                                        ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
                                        ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                                        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                                        ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                                        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                                        ((nb064AlphaDummy000), a),
                                        ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
        (nb064AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb064SplitAlpha0002 x y z r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                            ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                            ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                            ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
                            ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
                            ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                            ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                            ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                            ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                            ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
                            ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                            ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                            ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                            ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
                            ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
                            ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                            ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                            ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                            ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                            ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
                            ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb064AlphaDummy008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb064AlphaDummy010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb064AlphaDummy023),
        (nb064AlphaDummy026 r a)), ((nb064AlphaDummy022), (nb064AlphaDummy025 r a)),
        ((nb064AlphaDummy021), (nb064AlphaDummy024 r a)), ((nb064AlphaDummy019),
        (nb064AlphaDummy020 r a)), ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
        ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)), ((nb064AlphaDummy041),
        (nb064AlphaDummy042 r a)), ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
        ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)), ((nb064AlphaDummy007),
        (nb064AlphaDummy009 r a)), ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
        (nb064AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb064SplitAlpha0002 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                              ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                              ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                              ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
                              ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
                              ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                              ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                              ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                              ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                              ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
                              ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb064AlphaDummy019), (nb064AlphaDummy020 r a)),
                              ((nb064AlphaDummy015), (nb064AlphaDummy017 r a)),
                              ((nb064AlphaDummy016), (nb064AlphaDummy018 r a)),
                              ((nb064AlphaDummy041), (nb064AlphaDummy042 r a)),
                              ((nb064AlphaDummy039), (nb064AlphaDummy040 r a)),
                              ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                              ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                              ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                              ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                              ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
                              ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_pair_occurrence`. -/
@[expose]
noncomputable def nb064PairOccurrence (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaClass
      [((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Class.cv (nb064AlphaDummy005)) (Class.cv (nb064AlphaDummy006 x y z r a)) :=
  by
  have freshness0 : (nb064AlphaDummy005) ≠ (nb064AlphaDummy000) :=
    by
    unfold nb064AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0002) 0)))
  have freshness1 : (nb064AlphaDummy006 x y z r a) ≠ a :=
    by
    unfold nb064AlphaDummy006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0003 x y z r a) 0)))
  have freshness2 : (nb064AlphaDummy005) ≠ (nb064AlphaDummy001) :=
    by
    unfold nb064AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0000) 0)))
  have freshness3 : (nb064AlphaDummy006 x y z r a) ≠ r :=
    by
    unfold nb064AlphaDummy006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0001 x y z r a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0004`. -/
@[expose]
noncomputable def nb064SplitAlpha0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.classEq (Class.cv (nb064AlphaDummy005))
        (synCop (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy000))))
      (Wff.classEq (Class.cv (nb064AlphaDummy006 x y z r a))
        (synCop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (nb064PairOccurrence x y z r a) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb064SplitAlpha0001 x y z r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb064SplitAlpha0001 x y z r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy001))).fv ∪
                                    ((Class.cv (nb064AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb064SplitAlpha0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb064AlphaDummy039),
        (nb064AlphaDummy040 r a)), ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                                        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                                        ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                                        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                                        ((nb064AlphaDummy000), a),
                                        ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
        (nb064AlphaDummy006 x y z r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy001))).fv ∪
                                    ((Class.cv (nb064AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb064SplitAlpha0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb064AlphaDummy039),
        (nb064AlphaDummy040 r a)), ((nb064AlphaDummy008), (nb064AlphaDummy010 r a)),
                                        ((nb064AlphaDummy007), (nb064AlphaDummy009 r a)),
                                        ((nb064AlphaDummy037), (nb064AlphaDummy038 r a)),
                                        ((nb064AlphaDummy011), (nb064AlphaDummy012 r a)),
                                        ((nb064AlphaDummy000), a),
                                        ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
        (nb064AlphaDummy006 x y z r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0005`. -/
@[expose]
noncomputable def nb064SplitAlpha0005 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy063), (nb064AlphaDummy066 y z)),
        ((nb064AlphaDummy062), (nb064AlphaDummy065 y z)),
        ((nb064AlphaDummy061), (nb064AlphaDummy064 y z)),
        ((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
        ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
        ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
        ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
        ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
        ((nb064AlphaDummy053), (nb064AlphaDummy054 y z)),
        ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
        ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
        ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb064AlphaDummy061))
            (synCun (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy064 y z))
            (synCun (Class.cv (nb064AlphaDummy065 y z))
              (Class.cv (nb064AlphaDummy066 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb064AlphaDummy063), (nb064AlphaDummy066 y z)),
          ((nb064AlphaDummy062), (nb064AlphaDummy065 y z)),
          ((nb064AlphaDummy061), (nb064AlphaDummy064 y z)),
          ((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
          ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
          ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
          ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
          ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
          ((nb064AlphaDummy053), (nb064AlphaDummy054 y z)),
          ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
          ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
          ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
          ((nb064AlphaDummy001), r),
          ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C064C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0006`. -/
@[expose]
noncomputable def nb064SplitAlpha0006 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
        ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
        ((nb064AlphaDummy053), (nb064AlphaDummy054 y z)),
        ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
        ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
        ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy048))
          (Class.cv (nb064AlphaDummy003))) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy047))
            (synCphi (Class.cv (nb064AlphaDummy048))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy050 y z)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
            (synCphi (Class.cv (nb064AlphaDummy050 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0050) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0052 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0054) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0055 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0051) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0053 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb064AlphaDummy003))).fv ∪
                ((Class.cv (nb064AlphaDummy004))).fv) (by decide))
            (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb064AlphaDummy048))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb064AlphaDummy050 y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0060) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0061 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0060) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0061 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0058) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb064_support_mem_0059 y z) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb064AlphaDummy063),
        (nb064AlphaDummy066 y z)), ((nb064AlphaDummy062), (nb064AlphaDummy065 y z)),
        ((nb064AlphaDummy061), (nb064AlphaDummy064 y z)), ((nb064AlphaDummy059),
        (nb064AlphaDummy060 y z)), ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
        ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)), ((nb064AlphaDummy048),
        (nb064AlphaDummy050 y z)), ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
        ((nb064AlphaDummy053), (nb064AlphaDummy054 y z)), ((nb064AlphaDummy051),
        (nb064AlphaDummy052 y z)), ((nb064AlphaDummy003), y),
        ((nb064AlphaDummy004), z), ((nb064AlphaDummy002), x),
        ((nb064AlphaDummy000), a), ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
        (nb064AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb064SplitAlpha0005 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
                              ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
                              ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
                              ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                              ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                              ((nb064AlphaDummy053), (nb064AlphaDummy054 y z)),
                              ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                              ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                              ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                              ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
                                (nb064AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
                              ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
                              ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
                              ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                              ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                              ((nb064AlphaDummy053), (nb064AlphaDummy054 y z)),
                              ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                              ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                              ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                              ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
                                (nb064AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0007`. -/
@[expose]
noncomputable def nb064SplitAlpha0007 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy063), (nb064AlphaDummy066 y z)),
        ((nb064AlphaDummy062), (nb064AlphaDummy065 y z)),
        ((nb064AlphaDummy061), (nb064AlphaDummy064 y z)),
        ((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
        ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
        ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
        ((nb064AlphaDummy081), (nb064AlphaDummy082 y z)),
        ((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
        ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
        ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
        ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
        ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
        ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
        ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb064AlphaDummy061))
            (synCun (Class.cv (nb064AlphaDummy062)) (Class.cv (nb064AlphaDummy063))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb064AlphaDummy065 y z))
            (Class.cv (nb064AlphaDummy066 y z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy064 y z))
            (synCun (Class.cv (nb064AlphaDummy065 y z))
              (Class.cv (nb064AlphaDummy066 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0065 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0063 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0068) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0069 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0066) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0067 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb064AlphaDummy063), (nb064AlphaDummy066 y z)),
          ((nb064AlphaDummy062), (nb064AlphaDummy065 y z)),
          ((nb064AlphaDummy061), (nb064AlphaDummy064 y z)),
          ((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
          ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
          ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
          ((nb064AlphaDummy081), (nb064AlphaDummy082 y z)),
          ((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
          ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
          ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
          ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
          ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
          ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
          ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
          ((nb064AlphaDummy001), r),
          ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0073 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0071 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy055))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb064AlphaDummy057 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0076) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0077 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0074) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0075 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0008`. -/
@[expose]
noncomputable def nb064SplitAlpha0008 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
        ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
        ((nb064AlphaDummy081), (nb064AlphaDummy082 y z)),
        ((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
        ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
        ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
        ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
        ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
        ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
        ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy055))
          (Class.cv (nb064AlphaDummy048))) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy056))
            (synCif (Wff.classMem (Class.cv (nb064AlphaDummy055)) (synCnnc))
              (synCplc (Class.cv (nb064AlphaDummy055)) (synC1c))
              (Class.cv (nb064AlphaDummy055))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy057 y z))
          (Class.cv (nb064AlphaDummy050 y z))) (Wff.neg
          (Wff.classEq (Class.cv (nb064AlphaDummy058 y z))
            (synCif (Wff.classMem (Class.cv (nb064AlphaDummy057 y z)) (synCnnc))
              (synCplc (Class.cv (nb064AlphaDummy057 y z)) (synC1c))
              (Class.cv (nb064AlphaDummy057 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0056) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0057 y z) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0086) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0087 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0084) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0085 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb064AlphaDummy048))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb064AlphaDummy050 y z))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0060) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0061 y z) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0060) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb064_support_mem_0061 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0058) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb064AlphaDummy063), (nb064AlphaDummy066 y z)),
                                  ((nb064AlphaDummy062), (nb064AlphaDummy065 y z)),
                                  ((nb064AlphaDummy061), (nb064AlphaDummy064 y z)),
                                  ((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
                                  ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
                                  ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
                                  ((nb064AlphaDummy081), (nb064AlphaDummy082 y z)),
                                  ((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
                                  ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                                  ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                                  ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
                                  ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                                  ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                                  ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                                  ((nb064AlphaDummy001), r), ((nb064AlphaDummy005),
                                    (nb064AlphaDummy006 x y z r a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb064SplitAlpha0007 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
                      ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
                      ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
                      ((nb064AlphaDummy081), (nb064AlphaDummy082 y z)),
                      ((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
                      ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                      ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                      ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
                      ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                      ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                      ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                      ((nb064AlphaDummy001), r),
                      ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0058) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0059 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb064AlphaDummy059), (nb064AlphaDummy060 y z)),
                      ((nb064AlphaDummy055), (nb064AlphaDummy057 y z)),
                      ((nb064AlphaDummy056), (nb064AlphaDummy058 y z)),
                      ((nb064AlphaDummy081), (nb064AlphaDummy082 y z)),
                      ((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
                      ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                      ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                      ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
                      ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                      ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                      ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                      ((nb064AlphaDummy001), r),
                      ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0009`. -/
@[expose]
noncomputable def nb064SplitAlpha0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
        ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
        ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
        ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
        ((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy077))
          (Class.cab (nb064AlphaDummy047)
            (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
              (Wff.classEq (Class.cv (nb064AlphaDummy047))
                (synCun (synCphi (Class.cv (nb064AlphaDummy048))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb064AlphaDummy077))
            (Class.cab (nb064AlphaDummy047)
              (synWrex (nb064AlphaDummy048) (Class.cv (nb064AlphaDummy004))
                (Wff.classEq (Class.cv (nb064AlphaDummy047))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy048)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb064AlphaDummy078 y z))
          (Class.cab (nb064AlphaDummy049 y z)
            (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
              (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb064AlphaDummy078 y z))
            (Class.cab (nb064AlphaDummy049 y z)
              (synWrex (nb064AlphaDummy050 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb064AlphaDummy049 y z))
                  (synCun (synCphi (Class.cv (nb064AlphaDummy050 y z)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0082) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0083 y z) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0079) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0081 y z) 0))
                        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_y_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb064AlphaDummy003))).fv ∪
                      ((Class.cv (nb064AlphaDummy004))).fv) (by decide))
                  (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb064SplitAlpha0008 x y z r a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                    (nb064SplitAlpha0008 x y z r a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
                          ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                          ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                          ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
                          ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                          ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                          ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                          ((nb064AlphaDummy001), r),
                          ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0078) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0080 y z) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0082) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0083 y z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0079) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb064_support_mem_0081 y z) 0))
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (Ne.symm dv_y_z) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb064AlphaDummy003))).fv ∪
                        ((Class.cv (nb064AlphaDummy004))).fv) (by decide))
                    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb064SplitAlpha0008 x y z r a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb064SplitAlpha0008 x y z r a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb064AlphaDummy079), (nb064AlphaDummy080 y z)),
                            ((nb064AlphaDummy048), (nb064AlphaDummy050 y z)),
                            ((nb064AlphaDummy047), (nb064AlphaDummy049 y z)),
                            ((nb064AlphaDummy077), (nb064AlphaDummy078 y z)),
                            ((nb064AlphaDummy051), (nb064AlphaDummy052 y z)),
                            ((nb064AlphaDummy003), y), ((nb064AlphaDummy004), z),
                            ((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                            ((nb064AlphaDummy001), r),
                            ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb064_split_alpha_0010`. -/
@[expose]
noncomputable def nb064SplitAlpha0010 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (dv_r_z : r ≠ z)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb064AlphaDummy001), r),
        ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
      (Wff.all (nb064AlphaDummy000) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb064AlphaDummy005))
              (synCop (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy000))))
            (Wff.all (nb064AlphaDummy002) (Wff.imp (synWa
                  (synWss (Class.cv (nb064AlphaDummy002))
                    (Class.cv (nb064AlphaDummy000)))
                  (synWne (Class.cv (nb064AlphaDummy002)) (synC0)))
                (synWrex (nb064AlphaDummy004) (Class.cv (nb064AlphaDummy002))
                  (synWral (nb064AlphaDummy003) (Class.cv (nb064AlphaDummy002)) (Wff.imp
                      (synWbr (Class.cv (nb064AlphaDummy003))
                        (Class.cv (nb064AlphaDummy001)) (Class.cv (nb064AlphaDummy004)))
                      (Wff.objEq (nb064AlphaDummy003) (nb064AlphaDummy004))))))))))
      (Wff.all a (Wff.neg (synWa (Wff.classEq (Class.cv (nb064AlphaDummy006 x y z r a))
              (synCop (Class.cv r) (Class.cv a))) (Wff.all x (Wff.imp
                (synWa (synWss (Class.cv x) (Class.cv a)) (synWne (Class.cv x) (synC0)))
                (synWrex z (Class.cv x) (synWral y (Class.cv x)
                    (Wff.imp (synWbr (Class.cv y) (Class.cv r) (Class.cv z))
                      (Wff.objEq y z))))))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (nb064SplitAlpha0004 x y z r a dv_a_r)
        (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0044) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0045 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0042) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0043 x a) 0))
                                      (TAlphaVar.here _ _ _)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0048) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0049 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0046) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0047 x a) 0))
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_a_x (TAlphaVar.here _ _ _))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0044) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0045 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0042) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0043 x a) 0))
                                      (TAlphaVar.here _ _ _)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0048) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb064_support_mem_0049 x a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0046) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb064_support_mem_0047 x a) 0))
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_a_x (TAlphaVar.here _ _ _)))))))))))))
                (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfClosed
                    [((nb064AlphaDummy002), x), ((nb064AlphaDummy000), a),
                      ((nb064AlphaDummy001), r),
                      ((nb064AlphaDummy005), (nb064AlphaDummy006 x y z r a))]
                    (synC0) (by simp only [fv_syn_c0]))))) (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      dv_x_z (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.imp (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb064SplitAlpha0006 x y z r a))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb064SplitAlpha0006 x y z r a)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                      (nb064SplitAlpha0009 x y z r a dv_y_z))))))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                              (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (Ne.symm dv_y_z) (TAlphaVar.here _ _ _)))))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_found`. -/
@[expose]
noncomputable def nominalDfFound (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (__dv_a_y : a ≠ y) (__dv_a_z : a ≠ z)
    (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (dv_r_z : r ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCfound) (synCopab r a (.all x
            (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
              (synWrex z (.cv x) (synWral y (.cv x)
                  (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
            (nb064SplitAlpha0010 x y z r a dv_a_r dv_a_x dv_r_x dv_r_y dv_r_z dv_x_y
              dv_x_z dv_y_z))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
