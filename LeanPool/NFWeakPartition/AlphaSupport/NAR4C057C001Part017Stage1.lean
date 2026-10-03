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

@[expose]
noncomputable def nb057_composition_variable_occurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)),
        ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Class.cv (nb057_alpha_dummy_001)) (Class.cv f) :=
  by
  have freshness0 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_046) :=
    by
    unfold nb057_alpha_dummy_046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  have freshness1 : f ≠ (nb057_alpha_dummy_049 f) :=
    by
    unfold nb057_alpha_dummy_049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  have freshness2 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_045) :=
    by
    unfold nb057_alpha_dummy_045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1))
  have freshness3 : f ≠ (nb057_alpha_dummy_048 f) :=
    by
    unfold nb057_alpha_dummy_048
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1))
  have freshness4 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_044) :=
    by
    unfold nb057_alpha_dummy_044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0))
  have freshness5 : f ≠ (nb057_alpha_dummy_047 f) :=
    by
    unfold nb057_alpha_dummy_047
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0))
  have freshness6 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_050) :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0))
  have freshness7 : f ≠ (nb057_alpha_dummy_051 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0))
  have freshness8 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_042) :=
    by
    unfold nb057_alpha_dummy_042
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0204) 0))
  have freshness9 : f ≠ (nb057_alpha_dummy_043 f) :=
    by
    unfold nb057_alpha_dummy_043
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0205 f) 0))
  have freshness10 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_040) :=
    by
    unfold nb057_alpha_dummy_040
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0202) 0))
  have freshness11 : f ≠ (nb057_alpha_dummy_041 f) :=
    by
    unfold nb057_alpha_dummy_041
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0203 f) 0))
  have freshness12 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_000) :=
    by
    unfold nb057_alpha_dummy_001 nb057_alpha_dummy_000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness13 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13 (TAlphaVar.here _ _ _)))))))))

@[expose]
noncomputable def nb057_split_alpha_0031 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)),
        ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (syn_wbr (Class.cv (nb057_alpha_dummy_044))
          (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046)))
        (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_045)))))
      (Wff.imp (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb057_alpha_dummy_049 f))) (Wff.neg
          (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_048 f))))) :=
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
        (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv
        (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv
        (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0011 f a)))))))))
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
        (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv
        (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv
        (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_046))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0011 f a)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0014 f a))))))))
      (TAlphaClass.cab (TAlphaWff.ex
          (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0025 f a dv_a_f)))))) (TAlphaWff.neg
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
                                      (((Class.cv (nb057_alpha_dummy_046))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0027 f a)))))))))
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
                                      (((Class.cv (nb057_alpha_dummy_046))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0027 f a)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0030 f a))))))))
        (nb057_composition_variable_occurrence f a dv_a_f))))

theorem nb057_wpp_notmem_0588 : (nb057_alpha_dummy_042) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_042, fv_syn_cid] using (nb057_compact_fv_empty_0058)

theorem nb057_wpp_notmem_0589 (f : Var) : (nb057_alpha_dummy_043 f) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_043, fv_syn_cid] using (nb057_compact_fv_empty_0059 f)

theorem nb057_wpp_notmem_0590 : (nb057_alpha_dummy_040) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_040, fv_syn_cid] using (nb057_compact_fv_empty_0060)

theorem nb057_wpp_notmem_0591 (f : Var) : (nb057_alpha_dummy_041 f) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_041, fv_syn_cid] using (nb057_compact_fv_empty_0061 f)

theorem nb057_wpp_notmem_0592 : (nb057_alpha_dummy_000) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_000, fv_syn_cid] using (nb057_compact_fv_empty_0020)

theorem nb057_wpp_notmem_0593 (a : Var) : a ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb057_compact_fv_empty_0021 a)

theorem nb057_wpp_notmem_0594 : (nb057_alpha_dummy_001) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_001, fv_syn_cid] using (nb057_compact_fv_empty_0022)

theorem nb057_wpp_notmem_0595 (f : Var) : f ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb057_compact_fv_empty_0023 f)

theorem nb057_wpp_notmem_0596 : (nb057_alpha_dummy_002) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_002, fv_syn_cid] using (nb057_compact_fv_empty_0024)

theorem nb057_wpp_notmem_0597 (f : Var) (a : Var) :
    (nb057_alpha_dummy_003 f a) ∉ ((syn_cid)).fv := by
  simpa only [nb057_alpha_dummy_003, fv_syn_cid] using (nb057_compact_fv_empty_0025 f a)

theorem nb057_compact_envfresh_0042 (f : Var) (a : Var) :
    TEnvFresh
      [((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)),
        ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb057_alpha_dummy_042) (nb057_alpha_dummy_043 f)
      (nb057_wpp_notmem_0588) (nb057_wpp_notmem_0589 f)
      (TEnvFresh.consFresh (nb057_alpha_dummy_040) (nb057_alpha_dummy_041 f)
        (nb057_wpp_notmem_0590) (nb057_wpp_notmem_0591 f)
        (TEnvFresh.consFresh (nb057_alpha_dummy_000) a (nb057_wpp_notmem_0592)
          (nb057_wpp_notmem_0593 a)
          (TEnvFresh.consFresh (nb057_alpha_dummy_001) f (nb057_wpp_notmem_0594)
            (nb057_wpp_notmem_0595 f)
            (TEnvFresh.consFresh (nb057_alpha_dummy_002) (nb057_alpha_dummy_003 f a)
              (nb057_wpp_notmem_0596) (nb057_wpp_notmem_0597 f a)
              (TEnvFresh.nil ((syn_cid)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
