/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C056C001Part013Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C056C001Part013`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_wpp_refl_0035`. -/
@[expose]
noncomputable def nb056WppRefl0035 (f : Var) :
    TReflOn
      [((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
        ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
        ((nb056AlphaDummy000), f)]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb056_compact_envfresh_0035 f)

/-- Checked nominal proof certificate identified upstream as `nb056_compose_binder_occurrence`. -/
@[expose]
noncomputable def nb056ComposeBinderOccurrence (f : Var) :
    TAlphaClass
      [(nb056AlphaDummy006, (nb056AlphaDummy009 f)),
        (nb056AlphaDummy005, (nb056AlphaDummy008 f)),
        (nb056AlphaDummy011, (nb056AlphaDummy012 f)),
        (nb056AlphaDummy003, (nb056AlphaDummy004 f)),
        (nb056AlphaDummy001, (nb056AlphaDummy002 f)), (nb056AlphaDummy000, f)]
      (Class.cv nb056AlphaDummy011) (Class.cv (nb056AlphaDummy012 f)) :=
  by
  have freshness0 : nb056AlphaDummy011 ≠ nb056AlphaDummy006 :=
    by
    unfold nb056AlphaDummy011
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0002) 0)))
  have freshness1 : (nb056AlphaDummy012 f) ≠ (nb056AlphaDummy009 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0003 f) 0)))
  have freshness2 : nb056AlphaDummy011 ≠ nb056AlphaDummy005 :=
    by
    unfold nb056AlphaDummy011
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0000) 0)))
  have freshness3 : (nb056AlphaDummy012 f) ≠ (nb056AlphaDummy008 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0001 f) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0027`. -/
@[expose]
noncomputable def nb056SplitAlpha0027 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy001), (nb056AlphaDummy002 f)), ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy001)) (synCnin
            (synCcom (Class.cv (nb056AlphaDummy000))
              (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy001)) (synCnin
              (synCcom (Class.cv (nb056AlphaDummy000))
                (synCcnv (Class.cv (nb056AlphaDummy000)))) (synCid)))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy002 f))
          (synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy002 f))
            (synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classEq (nb056ComposeBinderOccurrence f) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0006 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0006 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0009 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0007 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb056SplitAlpha0001 f))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0004) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0006 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0006 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0009 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0007 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb056SplitAlpha0001 f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb056SplitAlpha0004 f)))))))))
                      (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0026 f))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                  ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                  ((nb056AlphaDummy000), f)] (synCid) (nb056WppRefl0035 f)))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classEq (nb056ComposeBinderOccurrence f) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0006 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0009 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0007 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (nb056SplitAlpha0001 f))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0006 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0008) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0009 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb056_support_mem_0005) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0007 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (nb056SplitAlpha0001 f))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb056SplitAlpha0004 f)))))))))
                        (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0026 f))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn
                  [((nb056AlphaDummy003), (nb056AlphaDummy004 f)),
                    ((nb056AlphaDummy001), (nb056AlphaDummy002 f)),
                    ((nb056AlphaDummy000), f)] (synCid) (nb056WppRefl0035 f)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part014`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0028`. -/
@[expose]
noncomputable def nb056SplitAlpha0028 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy029), (nb056AlphaDummy032 f)),
        ((nb056AlphaDummy028), (nb056AlphaDummy031 f)),
        ((nb056AlphaDummy027), (nb056AlphaDummy030 f)),
        ((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
        ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
        ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
        ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
        ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
        ((nb056AlphaDummy019), (nb056AlphaDummy020 f)),
        ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy027))
            (synCun (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy030 f))
            (synCun (Class.cv (nb056AlphaDummy031 f))
              (Class.cv (nb056AlphaDummy032 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy029), (nb056AlphaDummy032 f)),
          ((nb056AlphaDummy028), (nb056AlphaDummy031 f)),
          ((nb056AlphaDummy027), (nb056AlphaDummy030 f)),
          ((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
          ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
          ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
          ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
          ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
          ((nb056AlphaDummy019), (nb056AlphaDummy020 f)),
          ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0029`. -/
@[expose]
noncomputable def nb056SplitAlpha0029 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
        ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
        ((nb056AlphaDummy019), (nb056AlphaDummy020 f)),
        ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy014))
          (Class.cv (nb056AlphaDummy005))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy013))
            (synCphi (Class.cv (nb056AlphaDummy014))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy016 f))
          (Class.cv (nb056AlphaDummy008 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
            (synCphi (Class.cv (nb056AlphaDummy016 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0009 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0007 f) 0)) (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
                      ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                  (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb056AlphaDummy005))).fv ∪
                ((Class.cv (nb056AlphaDummy006))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy008 f))).fv ∪
                ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy014))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy016 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0015 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0015 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0013 f) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb056AlphaDummy029),
        (nb056AlphaDummy032 f)), ((nb056AlphaDummy028), (nb056AlphaDummy031 f)),
        ((nb056AlphaDummy027), (nb056AlphaDummy030 f)), ((nb056AlphaDummy025),
        (nb056AlphaDummy026 f)), ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
        ((nb056AlphaDummy022), (nb056AlphaDummy024 f)), ((nb056AlphaDummy014),
        (nb056AlphaDummy016 f)), ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
        ((nb056AlphaDummy019), (nb056AlphaDummy020 f)), ((nb056AlphaDummy017),
        (nb056AlphaDummy018 f)), ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)), ((nb056AlphaDummy011),
        (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb056SplitAlpha0028 f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
                              ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
                              ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
                              ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                              ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                              ((nb056AlphaDummy019), (nb056AlphaDummy020 f)),
                              ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                              ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                              ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                              ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                              ((nb056AlphaDummy000), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
                              ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
                              ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
                              ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                              ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                              ((nb056AlphaDummy019), (nb056AlphaDummy020 f)),
                              ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                              ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                              ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                              ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                              ((nb056AlphaDummy000), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0030`. -/
@[expose]
noncomputable def nb056SplitAlpha0030 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy029), (nb056AlphaDummy032 f)),
        ((nb056AlphaDummy028), (nb056AlphaDummy031 f)),
        ((nb056AlphaDummy027), (nb056AlphaDummy030 f)),
        ((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
        ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
        ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
        ((nb056AlphaDummy047), (nb056AlphaDummy048 f)),
        ((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
        ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
        ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
        ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
        ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy027))
            (synCun (Class.cv (nb056AlphaDummy028)) (Class.cv (nb056AlphaDummy029))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy031 f))
            (Class.cv (nb056AlphaDummy032 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy030 f))
            (synCun (Class.cv (nb056AlphaDummy031 f))
              (Class.cv (nb056AlphaDummy032 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0019 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0017 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0023 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0021 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy029), (nb056AlphaDummy032 f)),
          ((nb056AlphaDummy028), (nb056AlphaDummy031 f)),
          ((nb056AlphaDummy027), (nb056AlphaDummy030 f)),
          ((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
          ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
          ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
          ((nb056AlphaDummy047), (nb056AlphaDummy048 f)),
          ((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
          ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
          ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
          ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
          ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0027 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0025 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy021))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy023 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0031 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0029 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0031`. -/
@[expose]
noncomputable def nb056SplitAlpha0031 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
        ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
        ((nb056AlphaDummy047), (nb056AlphaDummy048 f)),
        ((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
        ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
        ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
        ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
        ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb056AlphaDummy021))
            (Class.cv (nb056AlphaDummy014))) (Wff.classEq (Class.cv (nb056AlphaDummy022))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy021)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy021)) (synC1c))
              (Class.cv (nb056AlphaDummy021))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb056AlphaDummy023 f))
            (Class.cv (nb056AlphaDummy016 f)))
          (Wff.classEq (Class.cv (nb056AlphaDummy024 f))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy023 f)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy023 f)) (synC1c))
              (Class.cv (nb056AlphaDummy023 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0010) 1))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0011 f) 1))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0040) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0041 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0038) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0039 f) 0))
                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy014))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy016 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0014) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0015 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0014) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0015 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0012) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy029), (nb056AlphaDummy032 f)),
                                  ((nb056AlphaDummy028), (nb056AlphaDummy031 f)),
                                  ((nb056AlphaDummy027), (nb056AlphaDummy030 f)),
                                  ((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
                                  ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
                                  ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
                                  ((nb056AlphaDummy047), (nb056AlphaDummy048 f)),
                                  ((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
                                  ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                                  ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                                  ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
                                  ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0030 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
                      ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
                      ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
                      ((nb056AlphaDummy047), (nb056AlphaDummy048 f)),
                      ((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
                      ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                      ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                      ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
                      ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0012) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0013 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy025), (nb056AlphaDummy026 f)),
                      ((nb056AlphaDummy021), (nb056AlphaDummy023 f)),
                      ((nb056AlphaDummy022), (nb056AlphaDummy024 f)),
                      ((nb056AlphaDummy047), (nb056AlphaDummy048 f)),
                      ((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
                      ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                      ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                      ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
                      ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0032`. -/
@[expose]
noncomputable def nb056SplitAlpha0032 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy017)) (synCcompl
            (Class.cab (nb056AlphaDummy013)
              (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy005))
                (Wff.classEq (Class.cv (nb056AlphaDummy013))
                  (synCphi (Class.cv (nb056AlphaDummy014)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy017)) (synCcompl
              (Class.cab (nb056AlphaDummy013)
                (synWrex (nb056AlphaDummy014) (Class.cv (nb056AlphaDummy006))
                  (Wff.classEq (Class.cv (nb056AlphaDummy013))
                    (synCun (synCphi (Class.cv (nb056AlphaDummy014)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy018 f)) (synCcompl
            (Class.cab (nb056AlphaDummy015 f)
              (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy008 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                  (synCphi (Class.cv (nb056AlphaDummy016 f)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy018 f)) (synCcompl
              (Class.cab (nb056AlphaDummy015 f)
                (synWrex (nb056AlphaDummy016 f) (Class.cv (nb056AlphaDummy009 f))
                  (Wff.classEq (Class.cv (nb056AlphaDummy015 f))
                    (synCun (synCphi (Class.cv (nb056AlphaDummy016 f)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0029 f)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0029 f))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0036) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0037 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0033) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0035 f) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb056AlphaDummy005))).fv ∪
                                ((Class.cv (nb056AlphaDummy006))).fv) (by decide))
                            (freshVar_injective (((Class.cv (nb056AlphaDummy008 f))).fv ∪
                                ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.all (nb056SplitAlpha0031 f))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.all (nb056SplitAlpha0031 f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
                                    ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                                    ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                                    ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
                                    ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                                    ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                    ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                    ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                    ((nb056AlphaDummy000), f)]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0036) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0037 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0033) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0035 f) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb056AlphaDummy005))).fv ∪
                                ((Class.cv (nb056AlphaDummy006))).fv) (by decide))
                            (freshVar_injective (((Class.cv (nb056AlphaDummy008 f))).fv ∪
                                ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.all (nb056SplitAlpha0031 f))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.all (nb056SplitAlpha0031 f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((nb056AlphaDummy045), (nb056AlphaDummy046 f)),
                                    ((nb056AlphaDummy014), (nb056AlphaDummy016 f)),
                                    ((nb056AlphaDummy013), (nb056AlphaDummy015 f)),
                                    ((nb056AlphaDummy043), (nb056AlphaDummy044 f)),
                                    ((nb056AlphaDummy017), (nb056AlphaDummy018 f)),
                                    ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                    ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                    ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                    ((nb056AlphaDummy000), f)]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part015`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0033`. -/
@[expose]
noncomputable def nb056SplitAlpha0033 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy065), (nb056AlphaDummy068 f)),
        ((nb056AlphaDummy064), (nb056AlphaDummy067 f)),
        ((nb056AlphaDummy063), (nb056AlphaDummy066 f)),
        ((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
        ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
        ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
        ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
        ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
        ((nb056AlphaDummy055), (nb056AlphaDummy056 f)),
        ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy063))
            (synCun (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy066 f))
            (synCun (Class.cv (nb056AlphaDummy067 f))
              (Class.cv (nb056AlphaDummy068 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy065), (nb056AlphaDummy068 f)),
          ((nb056AlphaDummy064), (nb056AlphaDummy067 f)),
          ((nb056AlphaDummy063), (nb056AlphaDummy066 f)),
          ((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
          ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
          ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
          ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
          ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
          ((nb056AlphaDummy055), (nb056AlphaDummy056 f)),
          ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0034`. -/
@[expose]
noncomputable def nb056SplitAlpha0034 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
        ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
        ((nb056AlphaDummy055), (nb056AlphaDummy056 f)),
        ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy050))
          (Class.cv (nb056AlphaDummy005))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy049))
            (synCphi (Class.cv (nb056AlphaDummy050))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy052 f))
          (Class.cv (nb056AlphaDummy008 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
            (synCphi (Class.cv (nb056AlphaDummy052 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0047 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0045 f) 0)) (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv ∪
                      ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                  (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                    (by decide)) (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056AlphaDummy000))).fv ∪
                        ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                    (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb056AlphaDummy005))).fv ∪
                ((Class.cv (nb056AlphaDummy007))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy008 f))).fv ∪
                ((Class.cv (nb056AlphaDummy010 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy050))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy052 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0053 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0053 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0051 f) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb056AlphaDummy065),
        (nb056AlphaDummy068 f)), ((nb056AlphaDummy064), (nb056AlphaDummy067 f)),
        ((nb056AlphaDummy063), (nb056AlphaDummy066 f)), ((nb056AlphaDummy061),
        (nb056AlphaDummy062 f)), ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
        ((nb056AlphaDummy058), (nb056AlphaDummy060 f)), ((nb056AlphaDummy050),
        (nb056AlphaDummy052 f)), ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
        ((nb056AlphaDummy055), (nb056AlphaDummy056 f)), ((nb056AlphaDummy053),
        (nb056AlphaDummy054 f)), ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)), ((nb056AlphaDummy005),
        (nb056AlphaDummy008 f)), ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb056SplitAlpha0033 f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
                              ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
                              ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
                              ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                              ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                              ((nb056AlphaDummy055), (nb056AlphaDummy056 f)),
                              ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                              ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                              ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                              ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                              ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                              ((nb056AlphaDummy000), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
                              ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
                              ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
                              ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                              ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                              ((nb056AlphaDummy055), (nb056AlphaDummy056 f)),
                              ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                              ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                              ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                              ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                              ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                              ((nb056AlphaDummy000), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0035`. -/
@[expose]
noncomputable def nb056SplitAlpha0035 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy065), (nb056AlphaDummy068 f)),
        ((nb056AlphaDummy064), (nb056AlphaDummy067 f)),
        ((nb056AlphaDummy063), (nb056AlphaDummy066 f)),
        ((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
        ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
        ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
        ((nb056AlphaDummy083), (nb056AlphaDummy084 f)),
        ((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
        ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
        ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
        ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
        ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy063))
            (synCun (Class.cv (nb056AlphaDummy064)) (Class.cv (nb056AlphaDummy065))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy067 f))
            (Class.cv (nb056AlphaDummy068 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy066 f))
            (synCun (Class.cv (nb056AlphaDummy067 f))
              (Class.cv (nb056AlphaDummy068 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0057 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0055 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0059 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy065), (nb056AlphaDummy068 f)),
          ((nb056AlphaDummy064), (nb056AlphaDummy067 f)),
          ((nb056AlphaDummy063), (nb056AlphaDummy066 f)),
          ((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
          ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
          ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
          ((nb056AlphaDummy083), (nb056AlphaDummy084 f)),
          ((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
          ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
          ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
          ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
          ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0065 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0063 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy057))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy059 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0067 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0036`. -/
@[expose]
noncomputable def nb056SplitAlpha0036 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
        ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
        ((nb056AlphaDummy083), (nb056AlphaDummy084 f)),
        ((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
        ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
        ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
        ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
        ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy057))
          (Class.cv (nb056AlphaDummy050))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy058))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy057)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy057)) (synC1c))
              (Class.cv (nb056AlphaDummy057))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy059 f))
          (Class.cv (nb056AlphaDummy052 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy060 f))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy059 f)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy059 f)) (synC1c))
              (Class.cv (nb056AlphaDummy059 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0048) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0049 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0078) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0079 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0076) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0077 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy050))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy052 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0052) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0053 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0052) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0053 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0050) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy065), (nb056AlphaDummy068 f)),
                                  ((nb056AlphaDummy064), (nb056AlphaDummy067 f)),
                                  ((nb056AlphaDummy063), (nb056AlphaDummy066 f)),
                                  ((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
                                  ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
                                  ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
                                  ((nb056AlphaDummy083), (nb056AlphaDummy084 f)),
                                  ((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
                                  ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                                  ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                                  ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
                                  ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0035 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
                      ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
                      ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
                      ((nb056AlphaDummy083), (nb056AlphaDummy084 f)),
                      ((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
                      ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                      ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                      ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
                      ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0050) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0051 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy061), (nb056AlphaDummy062 f)),
                      ((nb056AlphaDummy057), (nb056AlphaDummy059 f)),
                      ((nb056AlphaDummy058), (nb056AlphaDummy060 f)),
                      ((nb056AlphaDummy083), (nb056AlphaDummy084 f)),
                      ((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
                      ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                      ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                      ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
                      ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0037`. -/
@[expose]
noncomputable def nb056SplitAlpha0037 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
        ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy079))
          (Class.cab (nb056AlphaDummy049)
            (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
              (Wff.classEq (Class.cv (nb056AlphaDummy049))
                (synCun (synCphi (Class.cv (nb056AlphaDummy050))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056AlphaDummy079))
            (Class.cab (nb056AlphaDummy049)
              (synWrex (nb056AlphaDummy050) (Class.cv (nb056AlphaDummy007))
                (Wff.classEq (Class.cv (nb056AlphaDummy049))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy050)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy080 f))
          (Class.cab (nb056AlphaDummy051 f)
            (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy080 f))
            (Class.cab (nb056AlphaDummy051 f)
              (synWrex (nb056AlphaDummy052 f) (Class.cv (nb056AlphaDummy010 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy051 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy052 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0074) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0075 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0071) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0073 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy005))).fv ∪
                      ((Class.cv (nb056AlphaDummy007))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056AlphaDummy008 f))).fv ∪
                      ((Class.cv (nb056AlphaDummy010 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0036 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0036 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
                          ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                          ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                          ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
                          ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                          ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0074) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0075 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0071) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0073 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056AlphaDummy005))).fv ∪
                        ((Class.cv (nb056AlphaDummy007))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy008 f))).fv ∪
                        ((Class.cv (nb056AlphaDummy010 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0036 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0036 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb056AlphaDummy081), (nb056AlphaDummy082 f)),
                            ((nb056AlphaDummy050), (nb056AlphaDummy052 f)),
                            ((nb056AlphaDummy049), (nb056AlphaDummy051 f)),
                            ((nb056AlphaDummy079), (nb056AlphaDummy080 f)),
                            ((nb056AlphaDummy053), (nb056AlphaDummy054 f)),
                            ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                            ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                            ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                            ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                            ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part016`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0038`. -/
@[expose]
noncomputable def nb056SplitAlpha0038 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy107), (nb056AlphaDummy110 f)),
        ((nb056AlphaDummy106), (nb056AlphaDummy109 f)),
        ((nb056AlphaDummy105), (nb056AlphaDummy108 f)),
        ((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
        ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
        ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
        ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
        ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
        ((nb056AlphaDummy097), (nb056AlphaDummy098 f)),
        ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy105))
            (synCun (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy108 f))
            (synCun (Class.cv (nb056AlphaDummy109 f))
              (Class.cv (nb056AlphaDummy110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy107), (nb056AlphaDummy110 f)),
          ((nb056AlphaDummy106), (nb056AlphaDummy109 f)),
          ((nb056AlphaDummy105), (nb056AlphaDummy108 f)),
          ((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
          ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
          ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
          ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
          ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
          ((nb056AlphaDummy097), (nb056AlphaDummy098 f)),
          ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
          ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
          ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
          ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0039`. -/
@[expose]
noncomputable def nb056SplitAlpha0039 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
        ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
        ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
        ((nb056AlphaDummy097), (nb056AlphaDummy098 f)),
        ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.neg (Wff.all (nb056AlphaDummy099) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb056AlphaDummy099))
                (Class.cv (nb056AlphaDummy092)))
              (Wff.classEq (Class.cv (nb056AlphaDummy100))
                (synCif (Wff.classMem (Class.cv (nb056AlphaDummy099)) (synCnnc))
                  (synCplc (Class.cv (nb056AlphaDummy099)) (synC1c))
                  (Class.cv (nb056AlphaDummy099))))))))
      (Wff.neg (Wff.all (nb056AlphaDummy101 f) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb056AlphaDummy101 f))
                (Class.cv (nb056AlphaDummy094 f)))
              (Wff.classEq (Class.cv (nb056AlphaDummy102 f))
                (synCif (Wff.classMem (Class.cv (nb056AlphaDummy101 f)) (synCnnc))
                  (synCplc (Class.cv (nb056AlphaDummy101 f)) (synC1c))
                  (Class.cv (nb056AlphaDummy101 f)))))))) :=
  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0094) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0095 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy107), (nb056AlphaDummy110 f)),
                                  ((nb056AlphaDummy106), (nb056AlphaDummy109 f)),
                                  ((nb056AlphaDummy105), (nb056AlphaDummy108 f)),
                                  ((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
                                  ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
                                  ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
                                  ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                                  ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                                  ((nb056AlphaDummy097), (nb056AlphaDummy098 f)),
                                  ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                                  ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                                  ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                                  ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0038 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
                      ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
                      ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
                      ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                      ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                      ((nb056AlphaDummy097), (nb056AlphaDummy098 f)),
                      ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
                      ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
                      ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
                      ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                      ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                      ((nb056AlphaDummy097), (nb056AlphaDummy098 f)),
                      ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0040`. -/
@[expose]
noncomputable def nb056SplitAlpha0040 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy107), (nb056AlphaDummy110 f)),
        ((nb056AlphaDummy106), (nb056AlphaDummy109 f)),
        ((nb056AlphaDummy105), (nb056AlphaDummy108 f)),
        ((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
        ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
        ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
        ((nb056AlphaDummy125), (nb056AlphaDummy126 f)),
        ((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
        ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
        ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
        ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
        ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy105))
            (synCun (Class.cv (nb056AlphaDummy106)) (Class.cv (nb056AlphaDummy107))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy109 f))
            (Class.cv (nb056AlphaDummy110 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy108 f))
            (synCun (Class.cv (nb056AlphaDummy109 f))
              (Class.cv (nb056AlphaDummy110 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy107), (nb056AlphaDummy110 f)),
          ((nb056AlphaDummy106), (nb056AlphaDummy109 f)),
          ((nb056AlphaDummy105), (nb056AlphaDummy108 f)),
          ((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
          ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
          ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
          ((nb056AlphaDummy125), (nb056AlphaDummy126 f)),
          ((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
          ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
          ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
          ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
          ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
          ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
          ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
          ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy099))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy101 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0041`. -/
@[expose]
noncomputable def nb056SplitAlpha0041 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
        ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
        ((nb056AlphaDummy125), (nb056AlphaDummy126 f)),
        ((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
        ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
        ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
        ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
        ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy099))
          (Class.cv (nb056AlphaDummy092))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy100))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy099)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy099)) (synC1c))
              (Class.cv (nb056AlphaDummy099))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy101 f))
          (Class.cv (nb056AlphaDummy094 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy102 f))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy101 f)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy101 f)) (synC1c))
              (Class.cv (nb056AlphaDummy101 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0090) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0091 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0120) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0121 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0118) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0119 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy092))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy094 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0094) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0095 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0094) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0095 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0092) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy107), (nb056AlphaDummy110 f)),
                                  ((nb056AlphaDummy106), (nb056AlphaDummy109 f)),
                                  ((nb056AlphaDummy105), (nb056AlphaDummy108 f)),
                                  ((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
                                  ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
                                  ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
                                  ((nb056AlphaDummy125), (nb056AlphaDummy126 f)),
                                  ((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
                                  ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                                  ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                                  ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
                                  ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                                  ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                                  ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                                  ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0040 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
                      ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
                      ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
                      ((nb056AlphaDummy125), (nb056AlphaDummy126 f)),
                      ((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
                      ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                      ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                      ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
                      ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy103), (nb056AlphaDummy104 f)),
                      ((nb056AlphaDummy099), (nb056AlphaDummy101 f)),
                      ((nb056AlphaDummy100), (nb056AlphaDummy102 f)),
                      ((nb056AlphaDummy125), (nb056AlphaDummy126 f)),
                      ((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
                      ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                      ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                      ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
                      ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0042`. -/
@[expose]
noncomputable def nb056SplitAlpha0042 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
        ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy121))
          (Class.cab (nb056AlphaDummy091)
            (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
              (Wff.classEq (Class.cv (nb056AlphaDummy091))
                (synCun (synCphi (Class.cv (nb056AlphaDummy092))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056AlphaDummy121))
            (Class.cab (nb056AlphaDummy091)
              (synWrex (nb056AlphaDummy092) (Class.cv (nb056AlphaDummy086))
                (Wff.classEq (Class.cv (nb056AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy092)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy122 f))
          (Class.cab (nb056AlphaDummy093 f)
            (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy122 f))
            (Class.cab (nb056AlphaDummy093 f)
              (synWrex (nb056AlphaDummy094 f) (Class.cv (nb056AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy094 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0116) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0117 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0113) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0115 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy085))).fv ∪
                      ((Class.cv (nb056AlphaDummy086))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056AlphaDummy087 f))).fv ∪
                      ((Class.cv (nb056AlphaDummy088 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0041 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0041 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
                          ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                          ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                          ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
                          ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                          ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                          ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                          ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                          ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0116) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0117 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0113) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0115 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056AlphaDummy085))).fv ∪
                        ((Class.cv (nb056AlphaDummy086))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy087 f))).fv ∪
                        ((Class.cv (nb056AlphaDummy088 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0041 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0041 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb056AlphaDummy123), (nb056AlphaDummy124 f)),
                            ((nb056AlphaDummy092), (nb056AlphaDummy094 f)),
                            ((nb056AlphaDummy091), (nb056AlphaDummy093 f)),
                            ((nb056AlphaDummy121), (nb056AlphaDummy122 f)),
                            ((nb056AlphaDummy095), (nb056AlphaDummy096 f)),
                            ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                            ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                            ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                            ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                            ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                            ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                            ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                            ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part017`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0043`. -/
@[expose]
noncomputable def nb056SplitAlpha0043 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy143), (nb056AlphaDummy146 f)),
        ((nb056AlphaDummy142), (nb056AlphaDummy145 f)),
        ((nb056AlphaDummy141), (nb056AlphaDummy144 f)),
        ((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
        ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
        ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
        ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
        ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
        ((nb056AlphaDummy133), (nb056AlphaDummy134 f)),
        ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy141))
            (synCun (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy144 f))
            (synCun (Class.cv (nb056AlphaDummy145 f))
              (Class.cv (nb056AlphaDummy146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy143), (nb056AlphaDummy146 f)),
          ((nb056AlphaDummy142), (nb056AlphaDummy145 f)),
          ((nb056AlphaDummy141), (nb056AlphaDummy144 f)),
          ((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
          ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
          ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
          ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
          ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
          ((nb056AlphaDummy133), (nb056AlphaDummy134 f)),
          ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
          ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
          ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
          ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0044`. -/
@[expose]
noncomputable def nb056SplitAlpha0044 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
        ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
        ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
        ((nb056AlphaDummy133), (nb056AlphaDummy134 f)),
        ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.neg (Wff.all (nb056AlphaDummy135) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb056AlphaDummy135))
                (Class.cv (nb056AlphaDummy128)))
              (Wff.classEq (Class.cv (nb056AlphaDummy136))
                (synCif (Wff.classMem (Class.cv (nb056AlphaDummy135)) (synCnnc))
                  (synCplc (Class.cv (nb056AlphaDummy135)) (synC1c))
                  (Class.cv (nb056AlphaDummy135))))))))
      (Wff.neg (Wff.all (nb056AlphaDummy137 f) (Wff.neg (synWa
              (Wff.classMem (Class.cv (nb056AlphaDummy137 f))
                (Class.cv (nb056AlphaDummy130 f)))
              (Wff.classEq (Class.cv (nb056AlphaDummy138 f))
                (synCif (Wff.classMem (Class.cv (nb056AlphaDummy137 f)) (synCnnc))
                  (synCplc (Class.cv (nb056AlphaDummy137 f)) (synC1c))
                  (Class.cv (nb056AlphaDummy137 f)))))))) :=
  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 1))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 1))
              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0132) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0133 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0132) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0133 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0130) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy143), (nb056AlphaDummy146 f)),
                                  ((nb056AlphaDummy142), (nb056AlphaDummy145 f)),
                                  ((nb056AlphaDummy141), (nb056AlphaDummy144 f)),
                                  ((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
                                  ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
                                  ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
                                  ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                                  ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                                  ((nb056AlphaDummy133), (nb056AlphaDummy134 f)),
                                  ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                                  ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                                  ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                                  ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0043 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
                      ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
                      ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
                      ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                      ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                      ((nb056AlphaDummy133), (nb056AlphaDummy134 f)),
                      ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
                      ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
                      ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
                      ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                      ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                      ((nb056AlphaDummy133), (nb056AlphaDummy134 f)),
                      ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0045`. -/
@[expose]
noncomputable def nb056SplitAlpha0045 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy143), (nb056AlphaDummy146 f)),
        ((nb056AlphaDummy142), (nb056AlphaDummy145 f)),
        ((nb056AlphaDummy141), (nb056AlphaDummy144 f)),
        ((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
        ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
        ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
        ((nb056AlphaDummy161), (nb056AlphaDummy162 f)),
        ((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
        ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
        ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
        ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
        ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy141))
            (synCun (Class.cv (nb056AlphaDummy142)) (Class.cv (nb056AlphaDummy143))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy145 f))
            (Class.cv (nb056AlphaDummy146 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy144 f))
            (synCun (Class.cv (nb056AlphaDummy145 f))
              (Class.cv (nb056AlphaDummy146 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0136) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0137 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0134) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0135 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0139 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy143), (nb056AlphaDummy146 f)),
          ((nb056AlphaDummy142), (nb056AlphaDummy145 f)),
          ((nb056AlphaDummy141), (nb056AlphaDummy144 f)),
          ((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
          ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
          ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
          ((nb056AlphaDummy161), (nb056AlphaDummy162 f)),
          ((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
          ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
          ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
          ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
          ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
          ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
          ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
          ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0144) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0145 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0142) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0143 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy135))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy137 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0147 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0046`. -/
@[expose]
noncomputable def nb056SplitAlpha0046 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
        ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
        ((nb056AlphaDummy161), (nb056AlphaDummy162 f)),
        ((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
        ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
        ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
        ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
        ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy135))
          (Class.cv (nb056AlphaDummy128))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy136))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy135)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy135)) (synC1c))
              (Class.cv (nb056AlphaDummy135))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy137 f))
          (Class.cv (nb056AlphaDummy130 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy138 f))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy137 f)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy137 f)) (synC1c))
              (Class.cv (nb056AlphaDummy137 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0128) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0129 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0158) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0159 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0156) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0157 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy128))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy130 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0132) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0133 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0132) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0133 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0130) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy143), (nb056AlphaDummy146 f)),
                                  ((nb056AlphaDummy142), (nb056AlphaDummy145 f)),
                                  ((nb056AlphaDummy141), (nb056AlphaDummy144 f)),
                                  ((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
                                  ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
                                  ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
                                  ((nb056AlphaDummy161), (nb056AlphaDummy162 f)),
                                  ((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
                                  ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                                  ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                                  ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
                                  ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                                  ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                                  ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                                  ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0045 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
                      ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
                      ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
                      ((nb056AlphaDummy161), (nb056AlphaDummy162 f)),
                      ((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
                      ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                      ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                      ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
                      ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0130) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0131 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy139), (nb056AlphaDummy140 f)),
                      ((nb056AlphaDummy135), (nb056AlphaDummy137 f)),
                      ((nb056AlphaDummy136), (nb056AlphaDummy138 f)),
                      ((nb056AlphaDummy161), (nb056AlphaDummy162 f)),
                      ((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
                      ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                      ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                      ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
                      ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                      ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                      ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                      ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part018`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0047`. -/
@[expose]
noncomputable def nb056SplitAlpha0047 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
        ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
        ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy157))
          (Class.cab (nb056AlphaDummy127)
            (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
              (Wff.classEq (Class.cv (nb056AlphaDummy127))
                (synCun (synCphi (Class.cv (nb056AlphaDummy128))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056AlphaDummy157))
            (Class.cab (nb056AlphaDummy127)
              (synWrex (nb056AlphaDummy128) (Class.cv (nb056AlphaDummy085))
                (Wff.classEq (Class.cv (nb056AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy128)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy158 f))
          (Class.cab (nb056AlphaDummy129 f)
            (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy158 f))
            (Class.cab (nb056AlphaDummy129 f)
              (synWrex (nb056AlphaDummy130 f) (Class.cv (nb056AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy130 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0154) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0155 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0151) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0153 f) 0))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy086))).fv ∪
                      ((Class.cv (nb056AlphaDummy085))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056AlphaDummy088 f))).fv ∪
                      ((Class.cv (nb056AlphaDummy087 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0046 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0046 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
                          ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                          ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                          ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
                          ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                          ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                          ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                          ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                          ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0150) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0152 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0154) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0155 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0151) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0153 f) 0))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb056AlphaDummy000))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056AlphaDummy086))).fv ∪
                        ((Class.cv (nb056AlphaDummy085))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy088 f))).fv ∪
                        ((Class.cv (nb056AlphaDummy087 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0046 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0046 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb056AlphaDummy159), (nb056AlphaDummy160 f)),
                            ((nb056AlphaDummy128), (nb056AlphaDummy130 f)),
                            ((nb056AlphaDummy127), (nb056AlphaDummy129 f)),
                            ((nb056AlphaDummy157), (nb056AlphaDummy158 f)),
                            ((nb056AlphaDummy131), (nb056AlphaDummy132 f)),
                            ((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
                            ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
                            ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
                            ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                            ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                            ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                            ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                            ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_direct_variable_occurrence`. -/
@[expose]
noncomputable def nb056DirectVariableOccurrence (f : Var) :
    TAlphaClass
      [(nb056AlphaDummy086, (nb056AlphaDummy088 f)),
        (nb056AlphaDummy085, (nb056AlphaDummy087 f)),
        (nb056AlphaDummy089, (nb056AlphaDummy090 f)),
        (nb056AlphaDummy007, (nb056AlphaDummy010 f)),
        (nb056AlphaDummy006, (nb056AlphaDummy009 f)),
        (nb056AlphaDummy005, (nb056AlphaDummy008 f)),
        (nb056AlphaDummy011, (nb056AlphaDummy012 f)), (nb056AlphaDummy000, f)]
      (Class.cv nb056AlphaDummy000) (Class.cv f) :=
  by
  have freshness0 : nb056AlphaDummy000 ≠ nb056AlphaDummy086 :=
    by
    unfold nb056AlphaDummy086
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0170) 1))
  have freshness1 : f ≠ (nb056AlphaDummy088 f) :=
    by
    unfold nb056AlphaDummy088
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0171 f) 1))
  have freshness2 : nb056AlphaDummy000 ≠ nb056AlphaDummy085 :=
    by
    unfold nb056AlphaDummy085
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0170) 0))
  have freshness3 : f ≠ (nb056AlphaDummy087 f) :=
    by
    unfold nb056AlphaDummy087
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0171 f) 0))
  have freshness4 : nb056AlphaDummy000 ≠ nb056AlphaDummy089 :=
    by
    unfold nb056AlphaDummy089
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0168) 0))
  have freshness5 : f ≠ (nb056AlphaDummy090 f) :=
    by
    unfold nb056AlphaDummy090
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0169 f) 0))
  have freshness6 : nb056AlphaDummy000 ≠ nb056AlphaDummy007 :=
    by
    unfold nb056AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  have freshness7 : f ≠ (nb056AlphaDummy010 f) :=
    by
    unfold nb056AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  have freshness8 : nb056AlphaDummy000 ≠ nb056AlphaDummy006 :=
    by
    unfold nb056AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 1))
  have freshness9 : f ≠ (nb056AlphaDummy009 f) :=
    by
    unfold nb056AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 1))
  have freshness10 : nb056AlphaDummy000 ≠ nb056AlphaDummy005 :=
    by
    unfold nb056AlphaDummy005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 0))
  have freshness11 : f ≠ (nb056AlphaDummy008 f) :=
    by
    unfold nb056AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 0))
  have freshness12 : nb056AlphaDummy000 ≠ nb056AlphaDummy011 :=
    by
    unfold nb056AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0165) 0))
  have freshness13 : f ≠ (nb056AlphaDummy012 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0167 f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13 (TAlphaVar.here _ _ _)))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0048`. -/
@[expose]
noncomputable def nb056SplitAlpha0048 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy086), (nb056AlphaDummy088 f)),
        ((nb056AlphaDummy085), (nb056AlphaDummy087 f)),
        ((nb056AlphaDummy089), (nb056AlphaDummy090 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq (Class.cv (nb056AlphaDummy089))
          (synCop (Class.cv (nb056AlphaDummy085)) (Class.cv (nb056AlphaDummy086))))
        (Wff.neg (synWbr (Class.cv (nb056AlphaDummy086)) (Class.cv (nb056AlphaDummy000))
            (Class.cv (nb056AlphaDummy085)))))
      (Wff.imp (Wff.classEq (Class.cv (nb056AlphaDummy090 f))
          (synCop (Class.cv (nb056AlphaDummy087 f)) (Class.cv (nb056AlphaDummy088 f))))
        (Wff.neg (synWbr (Class.cv (nb056AlphaDummy088 f)) (Class.cv f)
            (Class.cv (nb056AlphaDummy087 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0082) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0083 f) 0)))
          (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0080) 0)))
            (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0081 f) 0)))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb056AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb056AlphaDummy085))).fv ∪
                                      ((Class.cv (nb056AlphaDummy086))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb056AlphaDummy087 f))).fv ∪
                                      ((Class.cv (nb056AlphaDummy088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _)))
                              (TAlphaClass.cab (nb056SplitAlpha0039 f)))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb056AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb056AlphaDummy085))).fv ∪
                                      ((Class.cv (nb056AlphaDummy086))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb056AlphaDummy087 f))).fv ∪
                                      ((Class.cv (nb056AlphaDummy088 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _)))
                              (TAlphaClass.cab (nb056SplitAlpha0039 f)))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb056SplitAlpha0042 f))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0122) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0122) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0126) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0127 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0123) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0125 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb056AlphaDummy086))).fv ∪
                                        ((Class.cv (nb056AlphaDummy085))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb056AlphaDummy088 f))).fv ∪
                                        ((Class.cv (nb056AlphaDummy087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb056SplitAlpha0044 f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0122) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0122) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0126) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0127 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0123) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0125 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb056AlphaDummy086))).fv ∪
                                        ((Class.cv (nb056AlphaDummy085))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb056AlphaDummy088 f))).fv ∪
                                        ((Class.cv (nb056AlphaDummy087 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb056SplitAlpha0044 f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb056SplitAlpha0047 f))))))))
        (nb056DirectVariableOccurrence f))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0049`. -/
@[expose]
noncomputable def nb056SplitAlpha0049 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
        ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
        ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
        ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
        ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
        ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
        ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
        ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy169), (nb056AlphaDummy170 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy177))
            (synCun (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy180 f))
            (synCun (Class.cv (nb056AlphaDummy181 f))
              (Class.cv (nb056AlphaDummy182 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
          ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
          ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
          ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
          ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
          ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
          ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
          ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
          ((nb056AlphaDummy169), (nb056AlphaDummy170 f)),
          ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0050`. -/
@[expose]
noncomputable def nb056SplitAlpha0050 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
        ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy169), (nb056AlphaDummy170 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy164))
          (Class.cv (nb056AlphaDummy007))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy163))
            (synCphi (Class.cv (nb056AlphaDummy164))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy166 f))
          (Class.cv (nb056AlphaDummy010 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
            (synCphi (Class.cv (nb056AlphaDummy166 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0172) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0174 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0176) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0177 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0173) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0175 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy007))).fv ∪
                ((Class.cv (nb056AlphaDummy006))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy010 f))).fv ∪
                ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb056AlphaDummy164))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy166 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0182) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb056_support_mem_0183 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0182) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0183 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb056_support_mem_0181 f) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb056AlphaDummy179),
        (nb056AlphaDummy182 f)), ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
        ((nb056AlphaDummy177), (nb056AlphaDummy180 f)), ((nb056AlphaDummy175),
        (nb056AlphaDummy176 f)), ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
        ((nb056AlphaDummy172), (nb056AlphaDummy174 f)), ((nb056AlphaDummy164),
        (nb056AlphaDummy166 f)), ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy169), (nb056AlphaDummy170 f)), ((nb056AlphaDummy167),
        (nb056AlphaDummy168 f)), ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)), ((nb056AlphaDummy005),
        (nb056AlphaDummy008 f)), ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb056SplitAlpha0049 f))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                              ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                              ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                              ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                              ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                              ((nb056AlphaDummy169), (nb056AlphaDummy170 f)),
                              ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                              ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                              ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                              ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                              ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                              ((nb056AlphaDummy000), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                              ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                              ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                              ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                              ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                              ((nb056AlphaDummy169), (nb056AlphaDummy170 f)),
                              ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                              ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                              ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                              ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                              ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                              ((nb056AlphaDummy000), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0051`. -/
@[expose]
noncomputable def nb056SplitAlpha0051 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
        ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
        ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
        ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
        ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
        ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
        ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
        ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
        ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
        ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb056AlphaDummy177))
            (synCun (Class.cv (nb056AlphaDummy178)) (Class.cv (nb056AlphaDummy179))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb056AlphaDummy181 f))
            (Class.cv (nb056AlphaDummy182 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy180 f))
            (synCun (Class.cv (nb056AlphaDummy181 f))
              (Class.cv (nb056AlphaDummy182 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0186) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0187 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0184) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0185 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0190) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0191 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0188) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0189 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
          ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
          ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
          ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
          ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
          ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
          ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
          ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
          ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
          ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
          ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
          ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)), ((nb056AlphaDummy000), f)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0194) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0195 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0192) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0193 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy171))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb056AlphaDummy173 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0198) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0199 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0196) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0197 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part019`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0052`. -/
@[expose]
noncomputable def nb056SplitAlpha0052 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
        ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
        ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
        ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
        ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
        ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
        ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy171))
          (Class.cv (nb056AlphaDummy164))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy172))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy171)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy171)) (synC1c))
              (Class.cv (nb056AlphaDummy171))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy173 f))
          (Class.cv (nb056AlphaDummy166 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb056AlphaDummy174 f))
            (synCif (Wff.classMem (Class.cv (nb056AlphaDummy173 f)) (synCnnc))
              (synCplc (Class.cv (nb056AlphaDummy173 f)) (synC1c))
              (Class.cv (nb056AlphaDummy173 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0178) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0179 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0208) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0209 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0206) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0207 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb056AlphaDummy164))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb056AlphaDummy166 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0182) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0183 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0182) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb056_support_mem_0183 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0180) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb056AlphaDummy179), (nb056AlphaDummy182 f)),
                                  ((nb056AlphaDummy178), (nb056AlphaDummy181 f)),
                                  ((nb056AlphaDummy177), (nb056AlphaDummy180 f)),
                                  ((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                                  ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                                  ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                                  ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
                                  ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                                  ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                                  ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                                  ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                                  ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                                  ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                                  ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                                  ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                                  ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                                  ((nb056AlphaDummy000), f)]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb056SplitAlpha0051 f)))))))) (TAlphaWff.classMem
                  (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                      ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                      ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                      ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
                      ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                      ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                      ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                      ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                      ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)] (synCnnc) (by simp only [fv_syn_cnnc])))))
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0180) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0181 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb056AlphaDummy175), (nb056AlphaDummy176 f)),
                      ((nb056AlphaDummy171), (nb056AlphaDummy173 f)),
                      ((nb056AlphaDummy172), (nb056AlphaDummy174 f)),
                      ((nb056AlphaDummy197), (nb056AlphaDummy198 f)),
                      ((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                      ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                      ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                      ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                      ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                      ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                      ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                      ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                      ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                      ((nb056AlphaDummy000), f)]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_split_alpha_0053`. -/
@[expose]
noncomputable def nb056SplitAlpha0053 (f : Var) :
    TAlphaWff
      [((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
        ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
        ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
        ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
        ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
        ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
        ((nb056AlphaDummy000), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy193))
          (Class.cab (nb056AlphaDummy163)
            (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
              (Wff.classEq (Class.cv (nb056AlphaDummy163))
                (synCun (synCphi (Class.cv (nb056AlphaDummy164))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb056AlphaDummy193))
            (Class.cab (nb056AlphaDummy163)
              (synWrex (nb056AlphaDummy164) (Class.cv (nb056AlphaDummy006))
                (Wff.classEq (Class.cv (nb056AlphaDummy163))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy164)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb056AlphaDummy194 f))
          (Class.cab (nb056AlphaDummy165 f)
            (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
              (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb056AlphaDummy194 f))
            (Class.cab (nb056AlphaDummy165 f)
              (synWrex (nb056AlphaDummy166 f) (Class.cv (nb056AlphaDummy009 f))
                (Wff.classEq (Class.cv (nb056AlphaDummy165 f))
                  (synCun (synCphi (Class.cv (nb056AlphaDummy166 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0204) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0205 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0201) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0203 f) 0))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb056AlphaDummy000))).fv ∪
                              ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb056AlphaDummy007))).fv ∪
                      ((Class.cv (nb056AlphaDummy006))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb056AlphaDummy010 f))).fv ∪
                      ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0052 f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb056SplitAlpha0052 f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                          ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                          ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                          ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                          ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                          ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                          ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                          ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                          ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                          ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0200) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0202 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0204) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0205 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0201) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0203 f) 0))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb056AlphaDummy000))).fv ∪
                                ((synCcnv (Class.cv (nb056AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb056AlphaDummy007))).fv ∪
                        ((Class.cv (nb056AlphaDummy006))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb056AlphaDummy010 f))).fv ∪
                        ((Class.cv (nb056AlphaDummy009 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0052 f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb056SplitAlpha0052 f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb056AlphaDummy195), (nb056AlphaDummy196 f)),
                            ((nb056AlphaDummy164), (nb056AlphaDummy166 f)),
                            ((nb056AlphaDummy163), (nb056AlphaDummy165 f)),
                            ((nb056AlphaDummy193), (nb056AlphaDummy194 f)),
                            ((nb056AlphaDummy167), (nb056AlphaDummy168 f)),
                            ((nb056AlphaDummy007), (nb056AlphaDummy010 f)),
                            ((nb056AlphaDummy006), (nb056AlphaDummy009 f)),
                            ((nb056AlphaDummy005), (nb056AlphaDummy008 f)),
                            ((nb056AlphaDummy011), (nb056AlphaDummy012 f)),
                            ((nb056AlphaDummy000), f)] (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb056_function_binder_occurrence`. -/
@[expose]
noncomputable def nb056FunctionBinderOccurrence (f : Var) :
    TAlphaClass
      [(nb056AlphaDummy006, (nb056AlphaDummy009 f)),
        (nb056AlphaDummy005, (nb056AlphaDummy008 f)),
        (nb056AlphaDummy011, (nb056AlphaDummy012 f)), (nb056AlphaDummy000, f)]
      (Class.cv nb056AlphaDummy011) (Class.cv (nb056AlphaDummy012 f)) :=
  by
  have freshness0 : nb056AlphaDummy011 ≠ nb056AlphaDummy006 :=
    by
    unfold nb056AlphaDummy011
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0002) 0)))
  have freshness1 : (nb056AlphaDummy012 f) ≠ (nb056AlphaDummy009 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0003 f) 0)))
  have freshness2 : nb056AlphaDummy011 ≠ nb056AlphaDummy005 :=
    by
    unfold nb056AlphaDummy011
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0000) 0)))
  have freshness3 : (nb056AlphaDummy012 f) ≠ (nb056AlphaDummy008 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0001 f) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as
`nb056_function_variable_occurrence`.
-/
@[expose]
noncomputable def nb056FunctionVariableOccurrence (f : Var) :
    TAlphaClass
      [(nb056AlphaDummy007, (nb056AlphaDummy010 f)),
        (nb056AlphaDummy006, (nb056AlphaDummy009 f)),
        (nb056AlphaDummy005, (nb056AlphaDummy008 f)),
        (nb056AlphaDummy011, (nb056AlphaDummy012 f)), (nb056AlphaDummy000, f)]
      (Class.cv nb056AlphaDummy000) (Class.cv f) :=
  by
  have freshness0 : nb056AlphaDummy000 ≠ nb056AlphaDummy007 :=
    by
    unfold nb056AlphaDummy007
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 2))
  have freshness1 : f ≠ (nb056AlphaDummy010 f) :=
    by
    unfold nb056AlphaDummy010
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 2))
  have freshness2 : nb056AlphaDummy000 ≠ nb056AlphaDummy006 :=
    by
    unfold nb056AlphaDummy006
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 1))
  have freshness3 : f ≠ (nb056AlphaDummy009 f) :=
    by
    unfold nb056AlphaDummy009
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 1))
  have freshness4 : nb056AlphaDummy000 ≠ nb056AlphaDummy005 :=
    by
    unfold nb056AlphaDummy005
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0164) 0))
  have freshness5 : f ≠ (nb056AlphaDummy008 f) :=
    by
    unfold nb056AlphaDummy008
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0166 f) 0))
  have freshness6 : nb056AlphaDummy000 ≠ nb056AlphaDummy011 :=
    by
    unfold nb056AlphaDummy011
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0165) 0))
  have freshness7 : f ≠ (nb056AlphaDummy012 f) :=
    by
    unfold nb056AlphaDummy012
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0167 f) 0))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.here _ _ _))))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_funs`. -/
@[expose]
noncomputable def nominalDfFuns (f : Var) :
    Nominal.NPrf (.classEq (synCfuns) (.cab f (synWfun (.cv f)))) := by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classEq
          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb056SplitAlpha0027 f))))
          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classEq (nb056FunctionBinderOccurrence f) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb056SplitAlpha0032 f))))) (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0034 f))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0034 f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb056SplitAlpha0037 f))))))))
                        (TAlphaClass.cab (TAlphaWff.ex
                            (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0048 f))))))
                      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0050 f))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.neg (nb056SplitAlpha0050 f)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb056SplitAlpha0053 f))))))))
                        (nb056FunctionVariableOccurrence f))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
