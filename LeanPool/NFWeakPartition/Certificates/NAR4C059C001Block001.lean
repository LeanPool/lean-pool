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

/-- Checked nominal proof certificate identified upstream as `nb059_wpp_refl_0001`. -/
@[expose]
noncomputable def nb059WppRefl0001 (R : Class) (S_cls : Class) (a : Var)
    (dv_S_a : a ∉ S_cls.fv) :
    TReflOn
      [((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (S_cls).fv :=
  TEnvFresh.reflOn (nb059_compact_envfresh_0001 R S_cls a dv_S_a)

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0000`. -/
@[expose]
noncomputable def nb059SplitAlpha0000 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059AlphaDummy033 R S_cls), (nb059AlphaDummy036 R a)),
        ((nb059AlphaDummy032 R S_cls), (nb059AlphaDummy035 R a)),
        ((nb059AlphaDummy031 R S_cls), (nb059AlphaDummy034 R a)),
        ((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
        ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
        ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
        ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
        ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
        ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
        ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
        ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy031 R S_cls))
            (synCun (Class.cv (nb059AlphaDummy032 R S_cls))
              (Class.cv (nb059AlphaDummy033 R S_cls))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy034 R a))
            (synCun (Class.cv (nb059AlphaDummy035 R a))
              (Class.cv (nb059AlphaDummy036 R a)))))) :=
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
                                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb059AlphaDummy033 R S_cls), (nb059AlphaDummy036 R a)),
          ((nb059AlphaDummy032 R S_cls), (nb059AlphaDummy035 R a)),
          ((nb059AlphaDummy031 R S_cls), (nb059AlphaDummy034 R a)),
          ((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
          ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
          ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
          ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
          ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
          ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
          ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
          ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
          ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
          ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
          ((nb059AlphaDummy000 R S_cls), a),
          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0001`. -/
@[expose]
noncomputable def nb059SplitAlpha0001 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
        ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
        ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
        ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
        ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.classEq (Class.cv (nb059AlphaDummy017 R S_cls))
        (synCphi (Class.cv (nb059AlphaDummy018 R S_cls))))
      (Wff.classEq (Class.cv (nb059AlphaDummy019 R a))
        (synCphi (Class.cv (nb059AlphaDummy020 R a)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb059AlphaDummy014 R S_cls))).fv ∪
            ((Class.cv (nb059AlphaDummy013 R S_cls))).fv) (by decide)) (freshVar_injective
          (((Class.cv (nb059AlphaDummy016 R a))).fv ∪
            ((Class.cv (nb059AlphaDummy015 R a))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0016 R S_cls) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0017 R a) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb059AlphaDummy018 R S_cls))).fv)
                  (by decide)) (freshVar_injective (((Class.cv (nb059AlphaDummy020 R a))).fv)
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
                                  (TAlphaClass.reflOfClosed [((nb059AlphaDummy033 R S_cls),
                                        (nb059AlphaDummy036 R a)),
                                      ((nb059AlphaDummy032 R S_cls),
                                        (nb059AlphaDummy035 R a)),
                                      ((nb059AlphaDummy031 R S_cls),
                                        (nb059AlphaDummy034 R a)),
                                      ((nb059AlphaDummy029 R S_cls),
                                        (nb059AlphaDummy030 R a)),
                                      ((nb059AlphaDummy025 R S_cls),
                                        (nb059AlphaDummy027 R a)),
                                      ((nb059AlphaDummy026 R S_cls),
                                        (nb059AlphaDummy028 R a)),
                                      ((nb059AlphaDummy018 R S_cls),
                                        (nb059AlphaDummy020 R a)),
                                      ((nb059AlphaDummy017 R S_cls),
                                        (nb059AlphaDummy019 R a)),
                                      ((nb059AlphaDummy023 R S_cls),
                                        (nb059AlphaDummy024 R a)),
                                      ((nb059AlphaDummy021 R S_cls),
                                        (nb059AlphaDummy022 R a)),
                                      ((nb059AlphaDummy014 R S_cls),
                                        (nb059AlphaDummy016 R a)),
                                      ((nb059AlphaDummy013 R S_cls),
                                        (nb059AlphaDummy015 R a)),
                                      ((nb059AlphaDummy011 R S_cls),
                                        (nb059AlphaDummy012 R a)),
                                      ((nb059AlphaDummy009 R S_cls),
                                        (nb059AlphaDummy010 R a)),
                                      ((nb059AlphaDummy000 R S_cls), a),
                                      ((nb059AlphaDummy002 R S_cls),
                                        (nb059AlphaDummy004 R S_cls a)),
                                      ((nb059AlphaDummy001 R S_cls),
                                        (nb059AlphaDummy003 R S_cls a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb059SplitAlpha0000 R S_cls a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
                          ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
                          ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
                          ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
                          ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
                          ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
                          ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
                          ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                          ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                          ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                          ((nb059AlphaDummy000 R S_cls), a),
                          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
                          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt
                          (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
                          ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
                          ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
                          ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
                          ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
                          ((nb059AlphaDummy023 R S_cls), (nb059AlphaDummy024 R a)),
                          ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
                          ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                          ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                          ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                          ((nb059AlphaDummy000 R S_cls), a),
                          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
                          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0002`. -/
@[expose]
noncomputable def nb059SplitAlpha0002 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059AlphaDummy033 R S_cls), (nb059AlphaDummy036 R a)),
        ((nb059AlphaDummy032 R S_cls), (nb059AlphaDummy035 R a)),
        ((nb059AlphaDummy031 R S_cls), (nb059AlphaDummy034 R a)),
        ((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
        ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
        ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
        ((nb059AlphaDummy051 R S_cls), (nb059AlphaDummy052 R a)),
        ((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
        ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
        ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
        ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
        ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
        ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb059AlphaDummy032 R S_cls))
            (Class.cv (nb059AlphaDummy033 R S_cls))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy031 R S_cls))
            (synCun (Class.cv (nb059AlphaDummy032 R S_cls))
              (Class.cv (nb059AlphaDummy033 R S_cls))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb059AlphaDummy035 R a))
            (Class.cv (nb059AlphaDummy036 R a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy034 R a))
            (synCun (Class.cv (nb059AlphaDummy035 R a))
              (Class.cv (nb059AlphaDummy036 R a)))))) :=
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
                                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
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
                                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                  ((synC1c)).fv) (by decide)) (freshVar_injective
                                (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt
                            (mem_lt_freshVar (nb059_support_mem_0028 R S_cls) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0029 R a) 0))
                          (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0026 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0027 R a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb059AlphaDummy033 R S_cls), (nb059AlphaDummy036 R a)),
          ((nb059AlphaDummy032 R S_cls), (nb059AlphaDummy035 R a)),
          ((nb059AlphaDummy031 R S_cls), (nb059AlphaDummy034 R a)),
          ((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
          ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
          ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
          ((nb059AlphaDummy051 R S_cls), (nb059AlphaDummy052 R a)),
          ((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
          ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
          ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
          ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
          ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
          ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
          ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
          ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
          ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
          ((nb059AlphaDummy000 R S_cls), a),
          ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
          ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) (by decide))
            (freshVar_injective
              (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                              (mem_lt_freshVar (nb059_support_mem_0032 R S_cls) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0033 R a) 0))
                            (TAlphaVar.there (Nat.ne_of_lt
                                (mem_lt_freshVar (nb059_support_mem_0030 R S_cls) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0031 R a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy025 R S_cls))).fv ∪
                                    ((synC1c)).fv) (by decide)) (freshVar_injective
                                  (((Class.cv (nb059AlphaDummy027 R a))).fv ∪ ((synC1c)).fv)
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

/-- Checked nominal proof certificate identified upstream as `nb059_split_alpha_0003`. -/
@[expose]
noncomputable def nb059SplitAlpha0003 (R : Class) (S_cls : Class) (a : Var) :
    TAlphaWff
      [((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
        ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
        ((nb059AlphaDummy051 R S_cls), (nb059AlphaDummy052 R a)),
        ((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
        ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
        ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
        ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
        ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
        ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
        ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
        ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
        ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
        ((nb059AlphaDummy000 R S_cls), a),
        ((nb059AlphaDummy002 R S_cls), (nb059AlphaDummy004 R S_cls a)),
        ((nb059AlphaDummy001 R S_cls), (nb059AlphaDummy003 R S_cls a))]
      (Wff.imp (Wff.classMem (Class.cv (nb059AlphaDummy025 R S_cls))
          (Class.cv (nb059AlphaDummy018 R S_cls))) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy026 R S_cls))
            (synCif (Wff.classMem (Class.cv (nb059AlphaDummy025 R S_cls)) (synCnnc))
              (synCplc (Class.cv (nb059AlphaDummy025 R S_cls)) (synC1c))
              (Class.cv (nb059AlphaDummy025 R S_cls))))))
      (Wff.imp (Wff.classMem (Class.cv (nb059AlphaDummy027 R a))
          (Class.cv (nb059AlphaDummy020 R a))) (Wff.neg
          (Wff.classEq (Class.cv (nb059AlphaDummy028 R a))
            (synCif (Wff.classMem (Class.cv (nb059AlphaDummy027 R a)) (synCnnc))
              (synCplc (Class.cv (nb059AlphaDummy027 R a)) (synC1c))
              (Class.cv (nb059AlphaDummy027 R a)))))) :=
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
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb059AlphaDummy018 R S_cls))).fv)
              (by decide))
            (freshVar_injective (((Class.cv (nb059AlphaDummy020 R a))).fv) (by decide))
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
                              (TAlphaClass.reflOfClosed [((nb059AlphaDummy033 R S_cls),
                                    (nb059AlphaDummy036 R a)),
                                  ((nb059AlphaDummy032 R S_cls),
                                    (nb059AlphaDummy035 R a)),
                                  ((nb059AlphaDummy031 R S_cls),
                                    (nb059AlphaDummy034 R a)),
                                  ((nb059AlphaDummy029 R S_cls),
                                    (nb059AlphaDummy030 R a)),
                                  ((nb059AlphaDummy025 R S_cls),
                                    (nb059AlphaDummy027 R a)),
                                  ((nb059AlphaDummy026 R S_cls),
                                    (nb059AlphaDummy028 R a)),
                                  ((nb059AlphaDummy051 R S_cls),
                                    (nb059AlphaDummy052 R a)),
                                  ((nb059AlphaDummy049 R S_cls),
                                    (nb059AlphaDummy050 R a)),
                                  ((nb059AlphaDummy018 R S_cls),
                                    (nb059AlphaDummy020 R a)),
                                  ((nb059AlphaDummy017 R S_cls),
                                    (nb059AlphaDummy019 R a)),
                                  ((nb059AlphaDummy047 R S_cls),
                                    (nb059AlphaDummy048 R a)),
                                  ((nb059AlphaDummy021 R S_cls),
                                    (nb059AlphaDummy022 R a)),
                                  ((nb059AlphaDummy014 R S_cls),
                                    (nb059AlphaDummy016 R a)),
                                  ((nb059AlphaDummy013 R S_cls),
                                    (nb059AlphaDummy015 R a)),
                                  ((nb059AlphaDummy011 R S_cls),
                                    (nb059AlphaDummy012 R a)),
                                  ((nb059AlphaDummy009 R S_cls),
                                    (nb059AlphaDummy010 R a)),
                                  ((nb059AlphaDummy000 R S_cls), a),
                                  ((nb059AlphaDummy002 R S_cls),
                                    (nb059AlphaDummy004 R S_cls a)),
                                  ((nb059AlphaDummy001 R S_cls),
                                    (nb059AlphaDummy003 R S_cls a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb059SplitAlpha0002 R S_cls a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
                      ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
                      ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
                      ((nb059AlphaDummy051 R S_cls), (nb059AlphaDummy052 R a)),
                      ((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
                      ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
                      ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
                      ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
                      ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
                      ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                      ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                      ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                      ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                      ((nb059AlphaDummy000 R S_cls), a), ((nb059AlphaDummy002 R S_cls),
                        (nb059AlphaDummy004 R S_cls a)), ((nb059AlphaDummy001 R S_cls),
                        (nb059AlphaDummy003 R S_cls a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0018 R S_cls) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0019 R a) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb059AlphaDummy029 R S_cls), (nb059AlphaDummy030 R a)),
                      ((nb059AlphaDummy025 R S_cls), (nb059AlphaDummy027 R a)),
                      ((nb059AlphaDummy026 R S_cls), (nb059AlphaDummy028 R a)),
                      ((nb059AlphaDummy051 R S_cls), (nb059AlphaDummy052 R a)),
                      ((nb059AlphaDummy049 R S_cls), (nb059AlphaDummy050 R a)),
                      ((nb059AlphaDummy018 R S_cls), (nb059AlphaDummy020 R a)),
                      ((nb059AlphaDummy017 R S_cls), (nb059AlphaDummy019 R a)),
                      ((nb059AlphaDummy047 R S_cls), (nb059AlphaDummy048 R a)),
                      ((nb059AlphaDummy021 R S_cls), (nb059AlphaDummy022 R a)),
                      ((nb059AlphaDummy014 R S_cls), (nb059AlphaDummy016 R a)),
                      ((nb059AlphaDummy013 R S_cls), (nb059AlphaDummy015 R a)),
                      ((nb059AlphaDummy011 R S_cls), (nb059AlphaDummy012 R a)),
                      ((nb059AlphaDummy009 R S_cls), (nb059AlphaDummy010 R a)),
                      ((nb059AlphaDummy000 R S_cls), a), ((nb059AlphaDummy002 R S_cls),
                        (nb059AlphaDummy004 R S_cls a)), ((nb059AlphaDummy001 R S_cls),
                        (nb059AlphaDummy003 R S_cls a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
