/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block004

/-! NF weak partition development: NAR4C057C001Part017. -/


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

/-- Checked nominal proof certificate identified upstream as
`nb057_composition_variable_occurrence`.
-/
@[expose]
noncomputable def nb057CompositionVariableOccurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy042), (nb057AlphaDummy043 f)),
        ((nb057AlphaDummy040), (nb057AlphaDummy041 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Class.cv (nb057AlphaDummy001)) (Class.cv f) :=
  by
  have freshness0 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy046) :=
    by
    unfold nb057AlphaDummy046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  have freshness1 : f ≠ (nb057AlphaDummy049 f) :=
    by
    unfold nb057AlphaDummy049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  have freshness2 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy045) :=
    by
    unfold nb057AlphaDummy045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1))
  have freshness3 : f ≠ (nb057AlphaDummy048 f) :=
    by
    unfold nb057AlphaDummy048
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1))
  have freshness4 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy044) :=
    by
    unfold nb057AlphaDummy044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0))
  have freshness5 : f ≠ (nb057AlphaDummy047 f) :=
    by
    unfold nb057AlphaDummy047
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0))
  have freshness6 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy050) :=
    by
    unfold nb057AlphaDummy050
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0))
  have freshness7 : f ≠ (nb057AlphaDummy051 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0))
  have freshness8 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy042) :=
    by
    unfold nb057AlphaDummy042
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0204) 0))
  have freshness9 : f ≠ (nb057AlphaDummy043 f) :=
    by
    unfold nb057AlphaDummy043
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0205 f) 0))
  have freshness10 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy040) :=
    by
    unfold nb057AlphaDummy040
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0202) 0))
  have freshness11 : f ≠ (nb057AlphaDummy041 f) :=
    by
    unfold nb057AlphaDummy041
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0203 f) 0))
  have freshness12 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy000) :=
    by
    unfold nb057AlphaDummy001 nb057AlphaDummy000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness13 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13 (TAlphaVar.here _ _ _)))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0031`. -/
@[expose]
noncomputable def nb057SplitAlpha0031 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy042), (nb057AlphaDummy043 f)),
        ((nb057AlphaDummy040), (nb057AlphaDummy041 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (synWbr (Class.cv (nb057AlphaDummy044))
          (synCcnv (Class.cv (nb057AlphaDummy001))) (Class.cv (nb057AlphaDummy046)))
        (Wff.neg (synWbr (Class.cv (nb057AlphaDummy046)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy045)))))
      (Wff.imp (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
          (Class.cv (nb057AlphaDummy049 f))) (Wff.neg
          (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy048 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv
        (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv (Class.cv
        (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057AlphaDummy044))).fv ∪
                                      ((Class.cv (nb057AlphaDummy046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057AlphaDummy047 f))).fv ∪
                                      ((Class.cv (nb057AlphaDummy049 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0011 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv
        (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv (Class.cv
        (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057AlphaDummy044))).fv ∪
                                      ((Class.cv (nb057AlphaDummy046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057AlphaDummy047 f))).fv ∪
                                      ((Class.cv (nb057AlphaDummy049 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0011 f a)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0014 f a))))))))
      (TAlphaClass.cab (TAlphaWff.ex
          (TAlphaWff.ex (TAlphaWff.neg (nb057SplitAlpha0025 f a dv_a_f)))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0214) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0214) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0218) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0219 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0215) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0217 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy046))).fv ∪
                                        ((Class.cv (nb057AlphaDummy045))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy049 f))).fv ∪
                                        ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0027 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0214) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0214) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0218) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0219 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0215) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0217 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy046))).fv ∪
                                        ((Class.cv (nb057AlphaDummy045))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy049 f))).fv ∪
                                        ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0027 f a)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0030 f a))))))))
        (nb057CompositionVariableOccurrence f a dv_a_f))))

theorem nb057_wpp_notmem_0588 : (nb057AlphaDummy042) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy042, fv_syn_cid] using (nb057_compact_fv_empty_0058)

theorem nb057_wpp_notmem_0589 (f : Var) : (nb057AlphaDummy043 f) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy043, fv_syn_cid] using (nb057_compact_fv_empty_0059 f)

theorem nb057_wpp_notmem_0590 : (nb057AlphaDummy040) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy040, fv_syn_cid] using (nb057_compact_fv_empty_0060)

theorem nb057_wpp_notmem_0591 (f : Var) : (nb057AlphaDummy041 f) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy041, fv_syn_cid] using (nb057_compact_fv_empty_0061 f)

theorem nb057_wpp_notmem_0592 : (nb057AlphaDummy000) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy000, fv_syn_cid] using (nb057_compact_fv_empty_0020)

theorem nb057_wpp_notmem_0593 (a : Var) : a ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb057_compact_fv_empty_0021 a)

theorem nb057_wpp_notmem_0594 : (nb057AlphaDummy001) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy001, fv_syn_cid] using (nb057_compact_fv_empty_0022)

theorem nb057_wpp_notmem_0595 (f : Var) : f ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb057_compact_fv_empty_0023 f)

theorem nb057_wpp_notmem_0596 : (nb057AlphaDummy002) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy002, fv_syn_cid] using (nb057_compact_fv_empty_0024)

theorem nb057_wpp_notmem_0597 (f : Var) (a : Var) :
    (nb057AlphaDummy003 f a) ∉ ((synCid)).fv := by
  simpa only [nb057AlphaDummy003, fv_syn_cid] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0042 (f : Var) (a : Var) :
    TEnvFresh
      [((nb057AlphaDummy042), (nb057AlphaDummy043 f)),
        ((nb057AlphaDummy040), (nb057AlphaDummy041 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb057AlphaDummy042) (nb057AlphaDummy043 f)
      (nb057_wpp_notmem_0588) (nb057_wpp_notmem_0589 f)
      (TEnvFresh.consFresh (nb057AlphaDummy040) (nb057AlphaDummy041 f)
        (nb057_wpp_notmem_0590) (nb057_wpp_notmem_0591 f)
        (TEnvFresh.consFresh (nb057AlphaDummy000) a (nb057_wpp_notmem_0592)
          (nb057_wpp_notmem_0593 a)
          (TEnvFresh.consFresh (nb057AlphaDummy001) f (nb057_wpp_notmem_0594)
            (nb057_wpp_notmem_0595 f)
            (TEnvFresh.consFresh (nb057AlphaDummy002) (nb057AlphaDummy003 f a)
              (nb057_wpp_notmem_0596) (nb057_wpp_notmem_0597 f a)
              (TEnvFresh.nil ((synCid)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
