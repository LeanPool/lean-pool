/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C060C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C060C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0000`. -/
@[expose]
noncomputable def nb060SplitAlpha0000 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy023), (nb060AlphaDummy026 r a)),
        ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
        ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)),
        ((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
        ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
        ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
        ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
        ((nb060AlphaDummy013), (nb060AlphaDummy014 r a)),
        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy021))
            (synCun (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy024 r a))
            (synCun (Class.cv (nb060AlphaDummy025 r a))
              (Class.cv (nb060AlphaDummy026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy023), (nb060AlphaDummy026 r a)),
          ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
          ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)),
          ((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
          ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
          ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
          ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
          ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
          ((nb060AlphaDummy013), (nb060AlphaDummy014 r a)),
          ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
          ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0001`. -/
@[expose]
noncomputable def nb060SplitAlpha0001 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
        ((nb060AlphaDummy013), (nb060AlphaDummy014 r a)),
        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy008))
          (Class.cv (nb060AlphaDummy001))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy007))
            (synCphi (Class.cv (nb060AlphaDummy008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy010 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy009 r a))
            (synCphi (Class.cv (nb060AlphaDummy010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060AlphaDummy001))).fv ∪
                ((Class.cv (nb060AlphaDummy000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060AlphaDummy010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb060AlphaDummy023),
        (nb060AlphaDummy026 r a)), ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
        ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)), ((nb060AlphaDummy019),
        (nb060AlphaDummy020 r a)), ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
        ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)), ((nb060AlphaDummy008),
        (nb060AlphaDummy010 r a)), ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
        ((nb060AlphaDummy013), (nb060AlphaDummy014 r a)), ((nb060AlphaDummy011),
        (nb060AlphaDummy012 r a)), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060SplitAlpha0000 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                              ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                              ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                              ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                              ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                              ((nb060AlphaDummy013), (nb060AlphaDummy014 r a)),
                              ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                              ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
                              ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                              ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                              ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                              ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                              ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                              ((nb060AlphaDummy013), (nb060AlphaDummy014 r a)),
                              ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                              ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
                              ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0002`. -/
@[expose]
noncomputable def nb060SplitAlpha0002 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy023), (nb060AlphaDummy026 r a)),
        ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
        ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)),
        ((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
        ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
        ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
        ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
        ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
        ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
        ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy021))
            (synCun (Class.cv (nb060AlphaDummy022)) (Class.cv (nb060AlphaDummy023))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy025 r a))
            (Class.cv (nb060AlphaDummy026 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy024 r a))
            (synCun (Class.cv (nb060AlphaDummy025 r a))
              (Class.cv (nb060AlphaDummy026 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy023), (nb060AlphaDummy026 r a)),
          ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
          ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)),
          ((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
          ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
          ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
          ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
          ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
          ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
          ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
          ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
          ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
          ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy015))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy017 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0003`. -/
@[expose]
noncomputable def nb060SplitAlpha0003 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
        ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
        ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
        ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy041))
          (synCphi (Class.cv (nb060AlphaDummy008)))) (Wff.neg
          (Wff.classMem (Class.cv (nb060AlphaDummy041))
            (synCphi (Class.cv (nb060AlphaDummy008))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy042 r a))
          (synCphi (Class.cv (nb060AlphaDummy010 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb060AlphaDummy042 r a))
            (synCphi (Class.cv (nb060AlphaDummy010 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy008))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb060AlphaDummy010 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb060AlphaDummy023),
        (nb060AlphaDummy026 r a)), ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
                                        ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)),
                                        ((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                                        ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                                        ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                                        ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
                                        ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
                                        ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                                        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                                        ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                                        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                                        ((nb060AlphaDummy000), a),
                                        ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb060SplitAlpha0002 x y z r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                            ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                            ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                            ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
                            ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
                            ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                            ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                            ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                            ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                            ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
                            ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                            ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                            ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                            ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
                            ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
                            ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                            ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                            ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                            ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                            ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
                            ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy008))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060AlphaDummy010 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb060AlphaDummy023),
        (nb060AlphaDummy026 r a)), ((nb060AlphaDummy022), (nb060AlphaDummy025 r a)),
        ((nb060AlphaDummy021), (nb060AlphaDummy024 r a)), ((nb060AlphaDummy019),
        (nb060AlphaDummy020 r a)), ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
        ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)), ((nb060AlphaDummy041),
        (nb060AlphaDummy042 r a)), ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
        ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)), ((nb060AlphaDummy007),
        (nb060AlphaDummy009 r a)), ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060SplitAlpha0002 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                              ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                              ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                              ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
                              ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
                              ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                              ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                              ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                              ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                              ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
                              ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy019), (nb060AlphaDummy020 r a)),
                              ((nb060AlphaDummy015), (nb060AlphaDummy017 r a)),
                              ((nb060AlphaDummy016), (nb060AlphaDummy018 r a)),
                              ((nb060AlphaDummy041), (nb060AlphaDummy042 r a)),
                              ((nb060AlphaDummy039), (nb060AlphaDummy040 r a)),
                              ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                              ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                              ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                              ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                              ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
                              ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as
`nb060_ordered_pair_binder_occurrence`.
-/
@[expose]
noncomputable def nb060OrderedPairBinderOccurrence (x : Var) (y : Var) (z : Var)
    (r : Var) (a : Var) :
    TAlphaClass
      [((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Class.cv (nb060AlphaDummy005)) (Class.cv (nb060AlphaDummy006 x y z r a)) :=
  by
  have freshness0 : (nb060AlphaDummy005) ≠ (nb060AlphaDummy000) :=
    by
    unfold nb060AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0002) 0)))
  have freshness1 : (nb060AlphaDummy006 x y z r a) ≠ a :=
    by
    unfold nb060AlphaDummy006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0003 x y z r a) 0)))
  have freshness2 : (nb060AlphaDummy005) ≠ (nb060AlphaDummy001) :=
    by
    unfold nb060AlphaDummy005
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0000) 0)))
  have freshness3 : (nb060AlphaDummy006 x y z r a) ≠ r :=
    by
    unfold nb060AlphaDummy006
    with_reducible
      exact
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0001 x y z r a) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0004`. -/
@[expose]
noncomputable def nb060SplitAlpha0004 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.classEq (Class.cv (nb060AlphaDummy005))
        (synCop (Class.cv (nb060AlphaDummy001)) (Class.cv (nb060AlphaDummy000))))
      (Wff.classEq (Class.cv (nb060AlphaDummy006 x y z r a))
        (synCop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (nb060OrderedPairBinderOccurrence x y z r a) (TAlphaClass.cab
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb060SplitAlpha0001 x y z r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex
                        (TAlphaWff.neg (nb060SplitAlpha0001 x y z r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy001))).fv ∪
                                    ((Class.cv (nb060AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb060SplitAlpha0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb060AlphaDummy039),
        (nb060AlphaDummy040 r a)), ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                                        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                                        ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                                        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                                        ((nb060AlphaDummy000), a),
                                        ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb060_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy001))).fv ∪
                                    ((Class.cv (nb060AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg
        (nb060SplitAlpha0003 x y z r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb060AlphaDummy039),
        (nb060AlphaDummy040 r a)), ((nb060AlphaDummy008), (nb060AlphaDummy010 r a)),
                                        ((nb060AlphaDummy007), (nb060AlphaDummy009 r a)),
                                        ((nb060AlphaDummy037), (nb060AlphaDummy038 r a)),
                                        ((nb060AlphaDummy011), (nb060AlphaDummy012 r a)),
                                        ((nb060AlphaDummy000), a),
                                        ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0005`. -/
@[expose]
noncomputable def nb060SplitAlpha0005 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy059), (nb060AlphaDummy062 x y)),
        ((nb060AlphaDummy058), (nb060AlphaDummy061 x y)),
        ((nb060AlphaDummy057), (nb060AlphaDummy060 x y)),
        ((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
        ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
        ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
        ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
        ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
        ((nb060AlphaDummy049), (nb060AlphaDummy050 x y)),
        ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy057))
            (synCun (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy060 x y))
            (synCun (Class.cv (nb060AlphaDummy061 x y))
              (Class.cv (nb060AlphaDummy062 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy059), (nb060AlphaDummy062 x y)),
          ((nb060AlphaDummy058), (nb060AlphaDummy061 x y)),
          ((nb060AlphaDummy057), (nb060AlphaDummy060 x y)),
          ((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
          ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
          ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
          ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
          ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
          ((nb060AlphaDummy049), (nb060AlphaDummy050 x y)),
          ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
          ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0006`. -/
@[expose]
noncomputable def nb060SplitAlpha0006 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    TAlphaWff
      [((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
        ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
        ((nb060AlphaDummy049), (nb060AlphaDummy050 x y)),
        ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy044))
          (Class.cv (nb060AlphaDummy002))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy043))
            (synCphi (Class.cv (nb060AlphaDummy044))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy046 x y)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
            (synCphi (Class.cv (nb060AlphaDummy046 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0044 x y) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0047 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0045 x y) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060AlphaDummy002))).fv ∪
                ((Class.cv (nb060AlphaDummy003))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy044))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060AlphaDummy046 x y))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0053 x y) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0053 x y) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0051 x y) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb060AlphaDummy059),
        (nb060AlphaDummy062 x y)), ((nb060AlphaDummy058), (nb060AlphaDummy061 x y)),
        ((nb060AlphaDummy057), (nb060AlphaDummy060 x y)), ((nb060AlphaDummy055),
        (nb060AlphaDummy056 x y)), ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
        ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)), ((nb060AlphaDummy044),
        (nb060AlphaDummy046 x y)), ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
        ((nb060AlphaDummy049), (nb060AlphaDummy050 x y)), ((nb060AlphaDummy047),
        (nb060AlphaDummy048 x y)), ((nb060AlphaDummy004), z),
        ((nb060AlphaDummy003), y), ((nb060AlphaDummy002), x),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060SplitAlpha0005 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
                              ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
                              ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
                              ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                              ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                              ((nb060AlphaDummy049), (nb060AlphaDummy050 x y)),
                              ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
                              ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
                              ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
                              ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                              ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                              ((nb060AlphaDummy049), (nb060AlphaDummy050 x y)),
                              ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part007`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0007`. -/
@[expose]
noncomputable def nb060SplitAlpha0007 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy059), (nb060AlphaDummy062 x y)),
        ((nb060AlphaDummy058), (nb060AlphaDummy061 x y)),
        ((nb060AlphaDummy057), (nb060AlphaDummy060 x y)),
        ((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
        ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
        ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
        ((nb060AlphaDummy077), (nb060AlphaDummy078 x y)),
        ((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
        ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
        ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
        ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
        ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy057))
            (synCun (Class.cv (nb060AlphaDummy058)) (Class.cv (nb060AlphaDummy059))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy061 x y))
            (Class.cv (nb060AlphaDummy062 x y))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy060 x y))
            (synCun (Class.cv (nb060AlphaDummy061 x y))
              (Class.cv (nb060AlphaDummy062 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0057 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0055 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0061 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0059 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy059), (nb060AlphaDummy062 x y)),
          ((nb060AlphaDummy058), (nb060AlphaDummy061 x y)),
          ((nb060AlphaDummy057), (nb060AlphaDummy060 x y)),
          ((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
          ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
          ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
          ((nb060AlphaDummy077), (nb060AlphaDummy078 x y)),
          ((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
          ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
          ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
          ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
          ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
          ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0065 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0063 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy051))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy053 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0069 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0067 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0008`. -/
@[expose]
noncomputable def nb060SplitAlpha0008 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
        ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
        ((nb060AlphaDummy077), (nb060AlphaDummy078 x y)),
        ((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
        ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
        ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
        ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
        ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy051))
          (Class.cv (nb060AlphaDummy044))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy052))
            (synCif (Wff.classMem (Class.cv (nb060AlphaDummy051)) (synCnnc))
              (synCplc (Class.cv (nb060AlphaDummy051)) (synC1c))
              (Class.cv (nb060AlphaDummy051))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy053 x y))
          (Class.cv (nb060AlphaDummy046 x y))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy054 x y))
            (synCif (Wff.classMem (Class.cv (nb060AlphaDummy053 x y)) (synCnnc))
              (synCplc (Class.cv (nb060AlphaDummy053 x y)) (synC1c))
              (Class.cv (nb060AlphaDummy053 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0048) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0049 x y) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0078) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0079 x y) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0076) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0077 x y) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy044))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb060AlphaDummy046 x y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0052) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0053 x y) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0052) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0053 x y) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0050) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb060AlphaDummy059), (nb060AlphaDummy062 x y)),
                                  ((nb060AlphaDummy058), (nb060AlphaDummy061 x y)),
                                  ((nb060AlphaDummy057), (nb060AlphaDummy060 x y)),
                                  ((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
                                  ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
                                  ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
                                  ((nb060AlphaDummy077), (nb060AlphaDummy078 x y)),
                                  ((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
                                  ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                                  ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                                  ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
                                  ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                                  ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                                  ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                                  ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                    (nb060AlphaDummy006 x y z r a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb060SplitAlpha0007 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
                      ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
                      ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
                      ((nb060AlphaDummy077), (nb060AlphaDummy078 x y)),
                      ((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
                      ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                      ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                      ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
                      ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                      ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                      ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                      ((nb060AlphaDummy001), r),
                      ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0051 x y) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb060AlphaDummy055), (nb060AlphaDummy056 x y)),
                      ((nb060AlphaDummy051), (nb060AlphaDummy053 x y)),
                      ((nb060AlphaDummy052), (nb060AlphaDummy054 x y)),
                      ((nb060AlphaDummy077), (nb060AlphaDummy078 x y)),
                      ((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
                      ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                      ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                      ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
                      ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                      ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                      ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                      ((nb060AlphaDummy001), r),
                      ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0009`. -/
@[expose]
noncomputable def nb060SplitAlpha0009 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
        ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy073))
          (Class.cab (nb060AlphaDummy043)
            (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
              (Wff.classEq (Class.cv (nb060AlphaDummy043))
                (synCun (synCphi (Class.cv (nb060AlphaDummy044))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb060AlphaDummy073))
            (Class.cab (nb060AlphaDummy043)
              (synWrex (nb060AlphaDummy044) (Class.cv (nb060AlphaDummy003))
                (Wff.classEq (Class.cv (nb060AlphaDummy043))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy044)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy074 x y))
          (Class.cab (nb060AlphaDummy045 x y)
            (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb060AlphaDummy074 x y))
            (Class.cab (nb060AlphaDummy045 x y)
              (synWrex (nb060AlphaDummy046 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb060AlphaDummy045 x y))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy046 x y)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0074) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0075 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0071) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0073 x y) 0))
                        (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy002))).fv ∪
                      ((Class.cv (nb060AlphaDummy003))).fv) (by decide))
                  (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb060SplitAlpha0008 x y z r a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                    (nb060SplitAlpha0008 x y z r a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
                          ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                          ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                          ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
                          ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                          ((nb060AlphaDummy001), r),
                          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0070) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0072 x y) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0074) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0075 x y) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0071) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0073 x y) 0))
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb060AlphaDummy002))).fv ∪
                        ((Class.cv (nb060AlphaDummy003))).fv) (by decide))
                    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb060SplitAlpha0008 x y z r a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb060SplitAlpha0008 x y z r a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb060AlphaDummy075), (nb060AlphaDummy076 x y)),
                            ((nb060AlphaDummy044), (nb060AlphaDummy046 x y)),
                            ((nb060AlphaDummy043), (nb060AlphaDummy045 x y)),
                            ((nb060AlphaDummy073), (nb060AlphaDummy074 x y)),
                            ((nb060AlphaDummy047), (nb060AlphaDummy048 x y)),
                            ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                            ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                            ((nb060AlphaDummy001), r),
                            ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0010`. -/
@[expose]
noncomputable def nb060SplitAlpha0010 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy095), (nb060AlphaDummy098 y z)),
        ((nb060AlphaDummy094), (nb060AlphaDummy097 y z)),
        ((nb060AlphaDummy093), (nb060AlphaDummy096 y z)),
        ((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
        ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
        ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
        ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
        ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
        ((nb060AlphaDummy085), (nb060AlphaDummy086 y z)),
        ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy093))
            (synCun (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy096 y z))
            (synCun (Class.cv (nb060AlphaDummy097 y z))
              (Class.cv (nb060AlphaDummy098 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy095), (nb060AlphaDummy098 y z)),
          ((nb060AlphaDummy094), (nb060AlphaDummy097 y z)),
          ((nb060AlphaDummy093), (nb060AlphaDummy096 y z)),
          ((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
          ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
          ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
          ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
          ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
          ((nb060AlphaDummy085), (nb060AlphaDummy086 y z)),
          ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
          ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part008`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0011`. -/
@[expose]
noncomputable def nb060SplitAlpha0011 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
        ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
        ((nb060AlphaDummy085), (nb060AlphaDummy086 y z)),
        ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy080))
          (Class.cv (nb060AlphaDummy003))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy079))
            (synCphi (Class.cv (nb060AlphaDummy080))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy082 y z)) (Class.cv y)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
            (synCphi (Class.cv (nb060AlphaDummy082 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0084) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0085 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0081) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0083 y z) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060AlphaDummy003))).fv ∪
                ((Class.cv (nb060AlphaDummy004))).fv) (by decide))
            (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy080))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060AlphaDummy082 y z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0090) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0091 y z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0090) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0091 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb060AlphaDummy095),
        (nb060AlphaDummy098 y z)), ((nb060AlphaDummy094), (nb060AlphaDummy097 y z)),
        ((nb060AlphaDummy093), (nb060AlphaDummy096 y z)), ((nb060AlphaDummy091),
        (nb060AlphaDummy092 y z)), ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
        ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)), ((nb060AlphaDummy080),
        (nb060AlphaDummy082 y z)), ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
        ((nb060AlphaDummy085), (nb060AlphaDummy086 y z)), ((nb060AlphaDummy083),
        (nb060AlphaDummy084 y z)), ((nb060AlphaDummy004), z),
        ((nb060AlphaDummy003), y), ((nb060AlphaDummy002), x),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060SplitAlpha0010 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
                              ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
                              ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
                              ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                              ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                              ((nb060AlphaDummy085), (nb060AlphaDummy086 y z)),
                              ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
                              ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
                              ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
                              ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                              ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                              ((nb060AlphaDummy085), (nb060AlphaDummy086 y z)),
                              ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0012`. -/
@[expose]
noncomputable def nb060SplitAlpha0012 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy095), (nb060AlphaDummy098 y z)),
        ((nb060AlphaDummy094), (nb060AlphaDummy097 y z)),
        ((nb060AlphaDummy093), (nb060AlphaDummy096 y z)),
        ((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
        ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
        ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
        ((nb060AlphaDummy113), (nb060AlphaDummy114 y z)),
        ((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
        ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
        ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
        ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
        ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy093))
            (synCun (Class.cv (nb060AlphaDummy094)) (Class.cv (nb060AlphaDummy095))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy097 y z))
            (Class.cv (nb060AlphaDummy098 y z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy096 y z))
            (synCun (Class.cv (nb060AlphaDummy097 y z))
              (Class.cv (nb060AlphaDummy098 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy095), (nb060AlphaDummy098 y z)),
          ((nb060AlphaDummy094), (nb060AlphaDummy097 y z)),
          ((nb060AlphaDummy093), (nb060AlphaDummy096 y z)),
          ((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
          ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
          ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
          ((nb060AlphaDummy113), (nb060AlphaDummy114 y z)),
          ((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
          ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
          ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
          ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
          ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
          ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy087))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy089 y z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0013`. -/
@[expose]
noncomputable def nb060SplitAlpha0013 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
        ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
        ((nb060AlphaDummy113), (nb060AlphaDummy114 y z)),
        ((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
        ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
        ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
        ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
        ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy087))
          (Class.cv (nb060AlphaDummy080))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy088))
            (synCif (Wff.classMem (Class.cv (nb060AlphaDummy087)) (synCnnc))
              (synCplc (Class.cv (nb060AlphaDummy087)) (synC1c))
              (Class.cv (nb060AlphaDummy087))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy089 y z))
          (Class.cv (nb060AlphaDummy082 y z))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy090 y z))
            (synCif (Wff.classMem (Class.cv (nb060AlphaDummy089 y z)) (synCnnc))
              (synCplc (Class.cv (nb060AlphaDummy089 y z)) (synC1c))
              (Class.cv (nb060AlphaDummy089 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0116) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0117 y z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0114) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0115 y z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy080))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb060AlphaDummy082 y z))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0090) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0091 y z) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0090) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0091 y z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb060AlphaDummy095), (nb060AlphaDummy098 y z)),
                                  ((nb060AlphaDummy094), (nb060AlphaDummy097 y z)),
                                  ((nb060AlphaDummy093), (nb060AlphaDummy096 y z)),
                                  ((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
                                  ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
                                  ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
                                  ((nb060AlphaDummy113), (nb060AlphaDummy114 y z)),
                                  ((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
                                  ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                                  ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                                  ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
                                  ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                                  ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                                  ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                                  ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                    (nb060AlphaDummy006 x y z r a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb060SplitAlpha0012 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
                      ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
                      ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
                      ((nb060AlphaDummy113), (nb060AlphaDummy114 y z)),
                      ((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
                      ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                      ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                      ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
                      ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                      ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                      ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                      ((nb060AlphaDummy001), r),
                      ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb060AlphaDummy091), (nb060AlphaDummy092 y z)),
                      ((nb060AlphaDummy087), (nb060AlphaDummy089 y z)),
                      ((nb060AlphaDummy088), (nb060AlphaDummy090 y z)),
                      ((nb060AlphaDummy113), (nb060AlphaDummy114 y z)),
                      ((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
                      ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                      ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                      ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
                      ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                      ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                      ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                      ((nb060AlphaDummy001), r),
                      ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0014`. -/
@[expose]
noncomputable def nb060SplitAlpha0014 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaClass
      [((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Class.cab (nb060AlphaDummy109) (synWnan
          (Wff.classMem (Class.cv (nb060AlphaDummy109)) (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                    (synCsn (synC0c))))))) (Wff.classMem (Class.cv (nb060AlphaDummy109))
            (Class.cab (nb060AlphaDummy079)
              (synWrex (nb060AlphaDummy080) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy079))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy080)))
                    (synCsn (synC0c)))))))))
      (Class.cab (nb060AlphaDummy110 y z) (synWnan
          (Wff.classMem (Class.cv (nb060AlphaDummy110 y z))
            (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                    (synCsn (synC0c)))))))
          (Wff.classMem (Class.cv (nb060AlphaDummy110 y z))
            (Class.cab (nb060AlphaDummy081 y z)
              (synWrex (nb060AlphaDummy082 y z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy081 y z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy082 y z)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0112) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0113 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0109) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0111 y z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060AlphaDummy003))).fv ∪
                          ((Class.cv (nb060AlphaDummy004))).fv) (by decide))
                      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0013 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0013 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
                              ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                              ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                              ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
                              ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCcompl (synCsn (synC0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0112) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0113 y z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0109) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0111 y z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060AlphaDummy003))).fv ∪
                          ((Class.cv (nb060AlphaDummy004))).fv) (by decide))
                      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0013 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0013 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy111), (nb060AlphaDummy112 y z)),
                              ((nb060AlphaDummy080), (nb060AlphaDummy082 y z)),
                              ((nb060AlphaDummy079), (nb060AlphaDummy081 y z)),
                              ((nb060AlphaDummy109), (nb060AlphaDummy110 y z)),
                              ((nb060AlphaDummy083), (nb060AlphaDummy084 y z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCcompl (synCsn (synC0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn,
                                fv_syn_c0c]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part009`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0015`. -/
@[expose]
noncomputable def nb060SplitAlpha0015 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy131), (nb060AlphaDummy134 x z)),
        ((nb060AlphaDummy130), (nb060AlphaDummy133 x z)),
        ((nb060AlphaDummy129), (nb060AlphaDummy132 x z)),
        ((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
        ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
        ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
        ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
        ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
        ((nb060AlphaDummy121), (nb060AlphaDummy122 x z)),
        ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy129))
            (synCun (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy132 x z))
            (synCun (Class.cv (nb060AlphaDummy133 x z))
              (Class.cv (nb060AlphaDummy134 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy131), (nb060AlphaDummy134 x z)),
          ((nb060AlphaDummy130), (nb060AlphaDummy133 x z)),
          ((nb060AlphaDummy129), (nb060AlphaDummy132 x z)),
          ((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
          ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
          ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
          ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
          ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
          ((nb060AlphaDummy121), (nb060AlphaDummy122 x z)),
          ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
          ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0016`. -/
@[expose]
noncomputable def nb060SplitAlpha0016 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    TAlphaWff
      [((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
        ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
        ((nb060AlphaDummy121), (nb060AlphaDummy122 x z)),
        ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy116))
          (Class.cv (nb060AlphaDummy002))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy115))
            (synCphi (Class.cv (nb060AlphaDummy116))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy118 x z)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
            (synCphi (Class.cv (nb060AlphaDummy118 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0118) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0120 x z) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0122) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0123 x z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0119) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0121 x z) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                    dv_x_y (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb060AlphaDummy002))).fv ∪
                ((Class.cv (nb060AlphaDummy004))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb060AlphaDummy116))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb060AlphaDummy118 x z))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0128) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb060_support_mem_0129 x z) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0128) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0129 x z) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0126) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb060_support_mem_0127 x z) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb060AlphaDummy131),
        (nb060AlphaDummy134 x z)), ((nb060AlphaDummy130), (nb060AlphaDummy133 x z)),
        ((nb060AlphaDummy129), (nb060AlphaDummy132 x z)), ((nb060AlphaDummy127),
        (nb060AlphaDummy128 x z)), ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
        ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)), ((nb060AlphaDummy116),
        (nb060AlphaDummy118 x z)), ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
        ((nb060AlphaDummy121), (nb060AlphaDummy122 x z)), ((nb060AlphaDummy119),
        (nb060AlphaDummy120 x z)), ((nb060AlphaDummy004), z),
        ((nb060AlphaDummy003), y), ((nb060AlphaDummy002), x),
        ((nb060AlphaDummy000), a), ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
        (nb060AlphaDummy006 x y z r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb060SplitAlpha0015 x y z r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
                              ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
                              ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
                              ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                              ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                              ((nb060AlphaDummy121), (nb060AlphaDummy122 x z)),
                              ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
                              ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
                              ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
                              ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                              ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                              ((nb060AlphaDummy121), (nb060AlphaDummy122 x z)),
                              ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0017`. -/
@[expose]
noncomputable def nb060SplitAlpha0017 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy131), (nb060AlphaDummy134 x z)),
        ((nb060AlphaDummy130), (nb060AlphaDummy133 x z)),
        ((nb060AlphaDummy129), (nb060AlphaDummy132 x z)),
        ((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
        ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
        ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
        ((nb060AlphaDummy149), (nb060AlphaDummy150 x z)),
        ((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
        ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
        ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
        ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
        ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb060AlphaDummy129))
            (synCun (Class.cv (nb060AlphaDummy130)) (Class.cv (nb060AlphaDummy131))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb060AlphaDummy133 x z))
            (Class.cv (nb060AlphaDummy134 x z))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy132 x z))
            (synCun (Class.cv (nb060AlphaDummy133 x z))
              (Class.cv (nb060AlphaDummy134 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0132) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0133 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0130) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0131 x z) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0137 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0135 x z) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb060AlphaDummy131), (nb060AlphaDummy134 x z)),
          ((nb060AlphaDummy130), (nb060AlphaDummy133 x z)),
          ((nb060AlphaDummy129), (nb060AlphaDummy132 x z)),
          ((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
          ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
          ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
          ((nb060AlphaDummy149), (nb060AlphaDummy150 x z)),
          ((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
          ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
          ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
          ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
          ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
          ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
          ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
          ((nb060AlphaDummy001), r),
          ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0140) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0141 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0138) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0139 x z) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy123))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb060AlphaDummy125 x z))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0145 x z) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0143 x z) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C060C001Part010`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0018`. -/
@[expose]
noncomputable def nb060SplitAlpha0018 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaWff
      [((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
        ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
        ((nb060AlphaDummy149), (nb060AlphaDummy150 x z)),
        ((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
        ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
        ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
        ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
        ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy123))
          (Class.cv (nb060AlphaDummy116))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy124))
            (synCif (Wff.classMem (Class.cv (nb060AlphaDummy123)) (synCnnc))
              (synCplc (Class.cv (nb060AlphaDummy123)) (synC1c))
              (Class.cv (nb060AlphaDummy123))))))
      (Wff.imp (Wff.classMem (Class.cv (nb060AlphaDummy125 x z))
          (Class.cv (nb060AlphaDummy118 x z))) (Wff.neg
          (Wff.classEq (Class.cv (nb060AlphaDummy126 x z))
            (synCif (Wff.classMem (Class.cv (nb060AlphaDummy125 x z)) (synCnnc))
              (synCplc (Class.cv (nb060AlphaDummy125 x z)) (synC1c))
              (Class.cv (nb060AlphaDummy125 x z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0124) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0125 x z) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0154) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0155 x z) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0152) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0153 x z) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb060AlphaDummy116))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb060AlphaDummy118 x z))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0128) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0129 x z) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0128) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb060_support_mem_0129 x z) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0126) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb060AlphaDummy131), (nb060AlphaDummy134 x z)),
                                  ((nb060AlphaDummy130), (nb060AlphaDummy133 x z)),
                                  ((nb060AlphaDummy129), (nb060AlphaDummy132 x z)),
                                  ((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
                                  ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
                                  ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
                                  ((nb060AlphaDummy149), (nb060AlphaDummy150 x z)),
                                  ((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
                                  ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                                  ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                                  ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
                                  ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                                  ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                                  ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                                  ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                    (nb060AlphaDummy006 x y z r a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb060SplitAlpha0017 x y z r a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
                      ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
                      ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
                      ((nb060AlphaDummy149), (nb060AlphaDummy150 x z)),
                      ((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
                      ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                      ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                      ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
                      ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                      ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                      ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                      ((nb060AlphaDummy001), r),
                      ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0126) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0127 x z) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb060AlphaDummy127), (nb060AlphaDummy128 x z)),
                      ((nb060AlphaDummy123), (nb060AlphaDummy125 x z)),
                      ((nb060AlphaDummy124), (nb060AlphaDummy126 x z)),
                      ((nb060AlphaDummy149), (nb060AlphaDummy150 x z)),
                      ((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
                      ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                      ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                      ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
                      ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                      ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                      ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                      ((nb060AlphaDummy001), r),
                      ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb060_split_alpha_0019`. -/
@[expose]
noncomputable def nb060SplitAlpha0019 (x : Var) (y : Var) (z : Var) (r : Var)
    (a : Var) :
    TAlphaClass
      [((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
        ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
        ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
        ((nb060AlphaDummy001), r),
        ((nb060AlphaDummy005), (nb060AlphaDummy006 x y z r a))]
      (Class.cab (nb060AlphaDummy145) (synWnan
          (Wff.classMem (Class.cv (nb060AlphaDummy145)) (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                    (synCsn (synC0c))))))) (Wff.classMem (Class.cv (nb060AlphaDummy145))
            (Class.cab (nb060AlphaDummy115)
              (synWrex (nb060AlphaDummy116) (Class.cv (nb060AlphaDummy004))
                (Wff.classEq (Class.cv (nb060AlphaDummy115))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy116)))
                    (synCsn (synC0c)))))))))
      (Class.cab (nb060AlphaDummy146 x z) (synWnan
          (Wff.classMem (Class.cv (nb060AlphaDummy146 x z))
            (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                    (synCsn (synC0c)))))))
          (Wff.classMem (Class.cv (nb060AlphaDummy146 x z))
            (Class.cab (nb060AlphaDummy117 x z)
              (synWrex (nb060AlphaDummy118 x z) (Class.cv z)
                (Wff.classEq (Class.cv (nb060AlphaDummy117 x z))
                  (synCun (synCphi (Class.cv (nb060AlphaDummy118 x z)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0150) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0151 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0147) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0149 x z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060AlphaDummy002))).fv ∪
                          ((Class.cv (nb060AlphaDummy004))).fv) (by decide))
                      (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0018 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0018 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
                              ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                              ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                              ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
                              ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCcompl (synCsn (synC0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0146) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0148 x z) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0150) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0151 x z) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0147) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0149 x z) 0))
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective
                        (((Class.cv (nb060AlphaDummy002))).fv ∪
                          ((Class.cv (nb060AlphaDummy004))).fv) (by decide))
                      (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (by decide))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0018 x y z r a)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb060SplitAlpha0018 x y z r a)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb060AlphaDummy147), (nb060AlphaDummy148 x z)),
                              ((nb060AlphaDummy116), (nb060AlphaDummy118 x z)),
                              ((nb060AlphaDummy115), (nb060AlphaDummy117 x z)),
                              ((nb060AlphaDummy145), (nb060AlphaDummy146 x z)),
                              ((nb060AlphaDummy119), (nb060AlphaDummy120 x z)),
                              ((nb060AlphaDummy004), z), ((nb060AlphaDummy003), y),
                              ((nb060AlphaDummy002), x), ((nb060AlphaDummy000), a),
                              ((nb060AlphaDummy001), r), ((nb060AlphaDummy005),
                                (nb060AlphaDummy006 x y z r a))]
                            (synCcompl (synCsn (synC0c))) (by
                              simp only [fv_syn_ccompl, fv_syn_csn,
                                fv_syn_c0c]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_trans`. -/
@[expose]
noncomputable def nominalDfTrans (x : Var) (y : Var) (z : Var) (r : Var) (a : Var)
    (dv_a_r : a ≠ r) (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (dv_a_z : a ≠ z) (dv_r_x : r ≠ x)
    (dv_r_y : r ≠ y) (dv_r_z : r ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCtrans) (synCopab r a (synWral x (.cv a) (synWral y (.cv a)
              (synWral z (.cv a) (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y))
                    (synWbr (.cv y) (.cv r) (.cv z)))
                  (synWbr (.cv x) (.cv r) (.cv z)))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb060SplitAlpha0004 x y z r a dv_a_r) (TAlphaWff.all
                (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                    (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_y
                            (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_x
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.all (TAlphaWff.imp
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_z
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_y
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_a_x (TAlphaVar.here _ _ _)))))) (TAlphaWff.imp
                            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060SplitAlpha0006 x y z r a dv_x_y dv_x_z))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060SplitAlpha0006 x y z r a dv_x_y dv_x_z))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb060SplitAlpha0009 x y z r a dv_y_z))))))))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_r_x (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (Ne.symm dv_a_r) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060SplitAlpha0011 x y z r a dv_y_z))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060SplitAlpha0011 x y z r a dv_y_z))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (nb060SplitAlpha0014 x y z r a))))) (TAlphaClass.cv
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) dv_r_x (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060SplitAlpha0016 x y z r a dv_x_y dv_x_z))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
        (nb060SplitAlpha0016 x y z r a dv_x_y dv_x_z))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (nb060SplitAlpha0019 x y z r a))))) (TAlphaClass.cv
                                (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_z
                                  (TAlphaVar.there
                                    (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_y
                                    (TAlphaVar.there
                                      (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
                                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var))
        (by decide)) (Ne.symm dv_a_r) (TAlphaVar.here _ _ _))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
