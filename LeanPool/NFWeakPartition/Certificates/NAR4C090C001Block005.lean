/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part017`. -/


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

theorem nb090_support_mem_0217 (h : Var) :
    (nb090_alpha_dummy_054 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_210 h) from (by
            unfold nb090_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0218 (A : Class) :
    (nb090_alpha_dummy_051 A) ∈
      (((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_207 A) from (by
          unfold nb090_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_051 A) ≠ (nb090_alpha_dummy_208 A) from (by
            unfold nb090_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0219 (h : Var) :
    (nb090_alpha_dummy_054 h) ∈
      (((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_054 h) ≠ (nb090_alpha_dummy_210 h) from (by
            unfold nb090_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0220 (A : Class) :
    (nb090_alpha_dummy_208 A) ∈ (((Class.cv (nb090_alpha_dummy_208 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0221 (h : Var) :
    (nb090_alpha_dummy_210 h) ∈ (((Class.cv (nb090_alpha_dummy_210 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0222 (A : Class) :
    (nb090_alpha_dummy_215 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_215 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0223 (h : Var) :
    (nb090_alpha_dummy_217 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_217 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0224 (A : Class) :
    (nb090_alpha_dummy_215 A) ∈
      (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0225 (h : Var) :
    (nb090_alpha_dummy_217 h) ∈
      (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0226 (A : Class) :
    (nb090_alpha_dummy_222 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0227 (h : Var) :
    (nb090_alpha_dummy_225 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0228 (A : Class) :
    (nb090_alpha_dummy_222 A) ∈
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0229 (h : Var) :
    (nb090_alpha_dummy_225 h) ∈
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0230 (A : Class) :
    (nb090_alpha_dummy_223 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
            (Class.cv (nb090_alpha_dummy_223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0231 (h : Var) :
    (nb090_alpha_dummy_226 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
            (Class.cv (nb090_alpha_dummy_226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0232 (A : Class) :
    (nb090_alpha_dummy_223 A) ∈
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0233 (h : Var) :
    (nb090_alpha_dummy_226 h) ∈
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0234 (A : Class) :
    (nb090_alpha_dummy_222 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0235 (h : Var) :
    (nb090_alpha_dummy_225 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0236 (A : Class) :
    (nb090_alpha_dummy_222 A) ∈
      (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_222 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0237 (h : Var) :
    (nb090_alpha_dummy_225 h) ∈
      (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_225 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0238 (A : Class) :
    (nb090_alpha_dummy_223 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0239 (h : Var) :
    (nb090_alpha_dummy_226 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0240 (A : Class) :
    (nb090_alpha_dummy_223 A) ∈
      (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_223 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0241 (h : Var) :
    (nb090_alpha_dummy_226 h) ∈
      (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0242 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0243 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_207 A)
              (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_207 A) from (by
          unfold nb090_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_208 A) from (by
            unfold nb090_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0244 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0245 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_209 h)
              (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_210 h) from (by
            unfold nb090_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0246 (A : Class) :
    (nb090_alpha_dummy_050 A) ∈
      (((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_207 A) from (by
          unfold nb090_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_050 A) ≠ (nb090_alpha_dummy_208 A) from (by
            unfold nb090_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0247 (h : Var) :
    (nb090_alpha_dummy_053 h) ∈
      (((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_209 h) from (by
          unfold nb090_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_053 h) ≠ (nb090_alpha_dummy_210 h) from (by
            unfold nb090_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0248 (A : Class) :
    (nb090_alpha_dummy_208 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0249 (h : Var) :
    (nb090_alpha_dummy_210 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0250 (A : Class) :
    (nb090_alpha_dummy_208 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0251 (h : Var) :
    (nb090_alpha_dummy_210 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0252 (A : Class) :
    (nb090_alpha_dummy_244 A) ∈
      (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0253 (A : Class) :
    (nb090_alpha_dummy_244 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_247 A) from (by
          unfold nb090_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_248 A) from (by
            unfold nb090_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0254 (h : Var) :
    (nb090_alpha_dummy_246 h) ∈
      (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0255 (h : Var) :
    (nb090_alpha_dummy_246 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_249 h) from (by
          unfold nb090_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_250 h) from (by
            unfold nb090_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0256 (A : Class) :
    (nb090_alpha_dummy_244 A) ∈
      (((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_247 A) from (by
          unfold nb090_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_244 A) ≠ (nb090_alpha_dummy_248 A) from (by
            unfold nb090_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0257 (h : Var) :
    (nb090_alpha_dummy_246 h) ∈
      (((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_249 h) from (by
          unfold nb090_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_246 h) ≠ (nb090_alpha_dummy_250 h) from (by
            unfold nb090_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0258 (A : Class) :
    (nb090_alpha_dummy_248 A) ∈ (((Class.cv (nb090_alpha_dummy_248 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0259 (h : Var) :
    (nb090_alpha_dummy_250 h) ∈ (((Class.cv (nb090_alpha_dummy_250 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0260 (A : Class) :
    (nb090_alpha_dummy_255 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_255 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0261 (h : Var) :
    (nb090_alpha_dummy_257 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_257 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0262 (A : Class) :
    (nb090_alpha_dummy_255 A) ∈
      (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0263 (h : Var) :
    (nb090_alpha_dummy_257 h) ∈
      (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0264 (A : Class) :
    (nb090_alpha_dummy_262 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0265 (h : Var) :
    (nb090_alpha_dummy_265 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0266 (A : Class) :
    (nb090_alpha_dummy_262 A) ∈
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0267 (h : Var) :
    (nb090_alpha_dummy_265 h) ∈
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0268 (A : Class) :
    (nb090_alpha_dummy_263 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
            (Class.cv (nb090_alpha_dummy_263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0269 (h : Var) :
    (nb090_alpha_dummy_266 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
            (Class.cv (nb090_alpha_dummy_266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0270 (A : Class) :
    (nb090_alpha_dummy_263 A) ∈
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0271 (h : Var) :
    (nb090_alpha_dummy_266 h) ∈
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0272 (A : Class) :
    (nb090_alpha_dummy_262 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0273 (h : Var) :
    (nb090_alpha_dummy_265 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0274 (A : Class) :
    (nb090_alpha_dummy_262 A) ∈
      (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_262 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0275 (h : Var) :
    (nb090_alpha_dummy_265 h) ∈
      (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_265 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0276 (A : Class) :
    (nb090_alpha_dummy_263 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0277 (h : Var) :
    (nb090_alpha_dummy_266 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0278 (A : Class) :
    (nb090_alpha_dummy_263 A) ∈
      (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_263 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0279 (h : Var) :
    (nb090_alpha_dummy_266 h) ∈
      (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_266 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0280 (A : Class) :
    (nb090_alpha_dummy_243 A) ∈
      (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0281 (A : Class) :
    (nb090_alpha_dummy_243 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_247 A)
              (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_247 A) from (by
          unfold nb090_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_248 A) from (by
            unfold nb090_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0282 (h : Var) :
    (nb090_alpha_dummy_245 h) ∈
      (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0283 (h : Var) :
    (nb090_alpha_dummy_245 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_249 h)
              (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_249 h) from (by
          unfold nb090_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_250 h) from (by
            unfold nb090_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0284 (A : Class) :
    (nb090_alpha_dummy_243 A) ∈
      (((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_247 A) from (by
          unfold nb090_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_243 A) ≠ (nb090_alpha_dummy_248 A) from (by
            unfold nb090_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0285 (h : Var) :
    (nb090_alpha_dummy_245 h) ∈
      (((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_249 h) from (by
          unfold nb090_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_245 h) ≠ (nb090_alpha_dummy_250 h) from (by
            unfold nb090_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0286 (A : Class) :
    (nb090_alpha_dummy_248 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0287 (h : Var) :
    (nb090_alpha_dummy_250 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0288 (A : Class) :
    (nb090_alpha_dummy_248 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0289 (h : Var) :
    (nb090_alpha_dummy_250 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0290 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0291 (h : Var) :
    h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0292 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0293 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
            (Class.cv (nb090_alpha_dummy_283 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0294 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_283 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_283 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_285 A) from (by
          unfold nb090_alpha_dummy_285;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0293 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_283 A) from (by
            unfold nb090_alpha_dummy_283;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0292 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0295 (u : Var) : u ∈ (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0296 (u : Var) :
    u ∈
      (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪
        ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0297 (u : Var) :
    u ∈
      (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_284 u)
              (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_286 u) from (by
          unfold nb090_alpha_dummy_286;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0296 u) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_284 u) from (by
            unfold nb090_alpha_dummy_284;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0295 u) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0298 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0299 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_291 A) from (by
          unfold nb090_alpha_dummy_291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_292 A) from (by
            unfold nb090_alpha_dummy_292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0300 (u : Var) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0301 (u : Var) :
    u ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_293 u) from (by
          unfold nb090_alpha_dummy_293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_294 u) from (by
            unfold nb090_alpha_dummy_294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0302 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_291 A) from (by
          unfold nb090_alpha_dummy_291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_292 A) from (by
            unfold nb090_alpha_dummy_292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0303 (u : Var) :
    u ∈
      (((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_293 u) from (by
          unfold nb090_alpha_dummy_293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_294 u) from (by
            unfold nb090_alpha_dummy_294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0304 (A : Class) :
    (nb090_alpha_dummy_292 A) ∈ (((Class.cv (nb090_alpha_dummy_292 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0305 (u : Var) :
    (nb090_alpha_dummy_294 u) ∈ (((Class.cv (nb090_alpha_dummy_294 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0306 (A : Class) :
    (nb090_alpha_dummy_299 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_299 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0307 (u : Var) :
    (nb090_alpha_dummy_301 u) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_301 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0308 (A : Class) :
    (nb090_alpha_dummy_299 A) ∈
      (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0309 (u : Var) :
    (nb090_alpha_dummy_301 u) ∈
      (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0310 (A : Class) :
    (nb090_alpha_dummy_306 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0311 (u : Var) :
    (nb090_alpha_dummy_309 u) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0312 (A : Class) :
    (nb090_alpha_dummy_306 A) ∈
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0313 (u : Var) :
    (nb090_alpha_dummy_309 u) ∈
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0314 (A : Class) :
    (nb090_alpha_dummy_307 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
            (Class.cv (nb090_alpha_dummy_307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0315 (u : Var) :
    (nb090_alpha_dummy_310 u) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
            (Class.cv (nb090_alpha_dummy_310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0316 (A : Class) :
    (nb090_alpha_dummy_307 A) ∈
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0317 (u : Var) :
    (nb090_alpha_dummy_310 u) ∈
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0318 (A : Class) :
    (nb090_alpha_dummy_306 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0319 (u : Var) :
    (nb090_alpha_dummy_309 u) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0320 (A : Class) :
    (nb090_alpha_dummy_306 A) ∈
      (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_306 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0321 (u : Var) :
    (nb090_alpha_dummy_309 u) ∈
      (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_309 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0322 (A : Class) :
    (nb090_alpha_dummy_307 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0323 (u : Var) :
    (nb090_alpha_dummy_310 u) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0324 (A : Class) :
    (nb090_alpha_dummy_307 A) ∈
      (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_307 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0325 (u : Var) :
    (nb090_alpha_dummy_310 u) ∈
      (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_310 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0326 (A : Class) :
    (nb090_alpha_dummy_283 A) ∈
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_283 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0327 (A : Class) :
    (nb090_alpha_dummy_283 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_291 A)
              (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_291 A) from (by
          unfold nb090_alpha_dummy_291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
            unfold nb090_alpha_dummy_292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0328 (u : Var) :
    (nb090_alpha_dummy_284 u) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0329 (u : Var) :
    (nb090_alpha_dummy_284 u) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_293 u)
              (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold nb090_alpha_dummy_293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
            unfold nb090_alpha_dummy_294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0330 (A : Class) :
    (nb090_alpha_dummy_283 A) ∈
      (((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_291 A) from (by
          unfold nb090_alpha_dummy_291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_283 A) ≠ (nb090_alpha_dummy_292 A) from (by
            unfold nb090_alpha_dummy_292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0331 (u : Var) :
    (nb090_alpha_dummy_284 u) ∈
      (((Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_293 u) from (by
          unfold nb090_alpha_dummy_293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_284 u) ≠ (nb090_alpha_dummy_294 u) from (by
            unfold nb090_alpha_dummy_294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0332 (A : Class) :
    (nb090_alpha_dummy_292 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0333 (u : Var) :
    (nb090_alpha_dummy_294 u) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0334 (A : Class) :
    (nb090_alpha_dummy_292 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0335 (u : Var) :
    (nb090_alpha_dummy_294 u) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0336 (A : Class) :
    (nb090_alpha_dummy_285 A) ∈ (((Class.cv (nb090_alpha_dummy_285 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0337 (u : Var) :
    (nb090_alpha_dummy_286 u) ∈ (((Class.cv (nb090_alpha_dummy_286 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0338 (A : Class) :
    (nb090_alpha_dummy_334 A) ∈
      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0339 (A : Class) :
    (nb090_alpha_dummy_334 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_337 A) from (by
          unfold nb090_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_338 A) from (by
            unfold nb090_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0340 (h : Var) :
    (nb090_alpha_dummy_336 h) ∈
      (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0341 (h : Var) :
    (nb090_alpha_dummy_336 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold nb090_alpha_dummy_339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_340 h) from (by
            unfold nb090_alpha_dummy_340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0342 (A : Class) :
    (nb090_alpha_dummy_334 A) ∈
      (((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_337 A) from (by
          unfold nb090_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_334 A) ≠ (nb090_alpha_dummy_338 A) from (by
            unfold nb090_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0343 (h : Var) :
    (nb090_alpha_dummy_336 h) ∈
      (((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold nb090_alpha_dummy_339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_336 h) ≠ (nb090_alpha_dummy_340 h) from (by
            unfold nb090_alpha_dummy_340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0344 (A : Class) :
    (nb090_alpha_dummy_338 A) ∈ (((Class.cv (nb090_alpha_dummy_338 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0345 (h : Var) :
    (nb090_alpha_dummy_340 h) ∈ (((Class.cv (nb090_alpha_dummy_340 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0346 (A : Class) :
    (nb090_alpha_dummy_345 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_345 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0347 (h : Var) :
    (nb090_alpha_dummy_347 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_347 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0348 (A : Class) :
    (nb090_alpha_dummy_345 A) ∈
      (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0349 (h : Var) :
    (nb090_alpha_dummy_347 h) ∈
      (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0350 (A : Class) :
    (nb090_alpha_dummy_352 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0351 (h : Var) :
    (nb090_alpha_dummy_355 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0352 (A : Class) :
    (nb090_alpha_dummy_352 A) ∈
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0353 (h : Var) :
    (nb090_alpha_dummy_355 h) ∈
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0354 (A : Class) :
    (nb090_alpha_dummy_353 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
            (Class.cv (nb090_alpha_dummy_353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0355 (h : Var) :
    (nb090_alpha_dummy_356 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
            (Class.cv (nb090_alpha_dummy_356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part018`. -/


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

theorem nb090_support_mem_0356 (A : Class) :
    (nb090_alpha_dummy_353 A) ∈
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0357 (h : Var) :
    (nb090_alpha_dummy_356 h) ∈
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0358 (A : Class) :
    (nb090_alpha_dummy_352 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0359 (h : Var) :
    (nb090_alpha_dummy_355 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0360 (A : Class) :
    (nb090_alpha_dummy_352 A) ∈
      (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0361 (h : Var) :
    (nb090_alpha_dummy_355 h) ∈
      (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0362 (A : Class) :
    (nb090_alpha_dummy_353 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0363 (h : Var) :
    (nb090_alpha_dummy_356 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0364 (A : Class) :
    (nb090_alpha_dummy_353 A) ∈
      (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0365 (h : Var) :
    (nb090_alpha_dummy_356 h) ∈
      (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0366 (A : Class) :
    (nb090_alpha_dummy_333 A) ∈
      (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0367 (A : Class) :
    (nb090_alpha_dummy_333 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_337 A)
              (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_337 A) from (by
          unfold nb090_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
            unfold nb090_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0368 (h : Var) :
    (nb090_alpha_dummy_335 h) ∈
      (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0369 (h : Var) :
    (nb090_alpha_dummy_335 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_339 h)
              (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold nb090_alpha_dummy_339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
            unfold nb090_alpha_dummy_340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0370 (A : Class) :
    (nb090_alpha_dummy_333 A) ∈
      (((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_337 A) from (by
          unfold nb090_alpha_dummy_337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_333 A) ≠ (nb090_alpha_dummy_338 A) from (by
            unfold nb090_alpha_dummy_338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0371 (h : Var) :
    (nb090_alpha_dummy_335 h) ∈
      (((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_339 h) from (by
          unfold nb090_alpha_dummy_339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_335 h) ≠ (nb090_alpha_dummy_340 h) from (by
            unfold nb090_alpha_dummy_340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0372 (A : Class) :
    (nb090_alpha_dummy_338 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0373 (h : Var) :
    (nb090_alpha_dummy_340 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0374 (A : Class) :
    (nb090_alpha_dummy_338 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0375 (h : Var) :
    (nb090_alpha_dummy_340 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0376 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0377 (v : Var) (h : Var) :
    h ∈
      (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0378 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0379 (v : Var) (h : Var) :
    h ∈ (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0380 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0381 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0382 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0383 (v : Var) (h : Var) :
    v ∈
      (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0384 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0385 (v : Var) (h : Var) :
    v ∈ (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0386 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0387 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
            (Class.cv (nb090_alpha_dummy_373 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0388 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
                (Class.cv (nb090_alpha_dummy_373 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_375 A) from (by
          unfold nb090_alpha_dummy_375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0387 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_373 A) from (by
            unfold nb090_alpha_dummy_373;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0386 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0389 (v : Var) : v ∈ (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0390 (v : Var) :
    v ∈
      (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪
        ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0391 (v : Var) :
    v ∈
      (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v)
              (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_376 v) from (by
          unfold nb090_alpha_dummy_376;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0390 v) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_374 v) from (by
            unfold nb090_alpha_dummy_374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0389 v) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0392 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0393 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_381 A) from (by
          unfold nb090_alpha_dummy_381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_382 A) from (by
            unfold nb090_alpha_dummy_382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0394 (v : Var) :
    v ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0395 (v : Var) :
    v ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_383 v) from (by
          unfold nb090_alpha_dummy_383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_384 v) from (by
            unfold nb090_alpha_dummy_384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0396 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_381 A) from (by
          unfold nb090_alpha_dummy_381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_382 A) from (by
            unfold nb090_alpha_dummy_382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0397 (v : Var) :
    v ∈
      (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_383 v) from (by
          unfold nb090_alpha_dummy_383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_384 v) from (by
            unfold nb090_alpha_dummy_384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0398 (A : Class) :
    (nb090_alpha_dummy_382 A) ∈ (((Class.cv (nb090_alpha_dummy_382 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0399 (v : Var) :
    (nb090_alpha_dummy_384 v) ∈ (((Class.cv (nb090_alpha_dummy_384 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0400 (A : Class) :
    (nb090_alpha_dummy_389 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_389 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0401 (v : Var) :
    (nb090_alpha_dummy_391 v) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_391 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0402 (A : Class) :
    (nb090_alpha_dummy_389 A) ∈
      (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0403 (v : Var) :
    (nb090_alpha_dummy_391 v) ∈
      (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0404 (A : Class) :
    (nb090_alpha_dummy_396 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0405 (v : Var) :
    (nb090_alpha_dummy_399 v) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0406 (A : Class) :
    (nb090_alpha_dummy_396 A) ∈
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0407 (v : Var) :
    (nb090_alpha_dummy_399 v) ∈
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0408 (A : Class) :
    (nb090_alpha_dummy_397 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
            (Class.cv (nb090_alpha_dummy_397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0409 (v : Var) :
    (nb090_alpha_dummy_400 v) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
            (Class.cv (nb090_alpha_dummy_400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0410 (A : Class) :
    (nb090_alpha_dummy_397 A) ∈
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0411 (v : Var) :
    (nb090_alpha_dummy_400 v) ∈
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0412 (A : Class) :
    (nb090_alpha_dummy_396 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0413 (v : Var) :
    (nb090_alpha_dummy_399 v) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0414 (A : Class) :
    (nb090_alpha_dummy_396 A) ∈
      (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0415 (v : Var) :
    (nb090_alpha_dummy_399 v) ∈
      (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0416 (A : Class) :
    (nb090_alpha_dummy_397 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0417 (v : Var) :
    (nb090_alpha_dummy_400 v) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0418 (A : Class) :
    (nb090_alpha_dummy_397 A) ∈
      (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0419 (v : Var) :
    (nb090_alpha_dummy_400 v) ∈
      (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0420 (A : Class) :
    (nb090_alpha_dummy_373 A) ∈
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0421 (A : Class) :
    (nb090_alpha_dummy_373 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_381 A)
              (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_373 A) ≠ (nb090_alpha_dummy_381 A) from (by
          unfold nb090_alpha_dummy_381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_373 A) ≠ (nb090_alpha_dummy_382 A) from (by
            unfold nb090_alpha_dummy_382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0422 (v : Var) :
    (nb090_alpha_dummy_374 v) ∈
      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0423 (v : Var) :
    (nb090_alpha_dummy_374 v) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_383 v)
              (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold nb090_alpha_dummy_383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
            unfold nb090_alpha_dummy_384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0424 (A : Class) :
    (nb090_alpha_dummy_373 A) ∈
      (((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_373 A) ≠ (nb090_alpha_dummy_381 A) from (by
          unfold nb090_alpha_dummy_381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_373 A) ≠ (nb090_alpha_dummy_382 A) from (by
            unfold nb090_alpha_dummy_382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0425 (v : Var) :
    (nb090_alpha_dummy_374 v) ∈
      (((Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_383 v) from (by
          unfold nb090_alpha_dummy_383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_374 v) ≠ (nb090_alpha_dummy_384 v) from (by
            unfold nb090_alpha_dummy_384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0426 (A : Class) :
    (nb090_alpha_dummy_382 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0427 (v : Var) :
    (nb090_alpha_dummy_384 v) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0428 (A : Class) :
    (nb090_alpha_dummy_382 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0429 (v : Var) :
    (nb090_alpha_dummy_384 v) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0430 (A : Class) :
    (nb090_alpha_dummy_375 A) ∈ (((Class.cv (nb090_alpha_dummy_375 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0431 (v : Var) :
    (nb090_alpha_dummy_376 v) ∈ (((Class.cv (nb090_alpha_dummy_376 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0432 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
                (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
                (Class.cv (nb090_alpha_dummy_425 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_424 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0433 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_427 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0434 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
                (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
                (Class.cv (nb090_alpha_dummy_425 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_424 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0435 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_427 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0436 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0437 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_431 A) from (by
          unfold nb090_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_432 A) from (by
            unfold nb090_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0438 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0439 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_433 h) from (by
          unfold nb090_alpha_dummy_433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_434 h) from (by
            unfold nb090_alpha_dummy_434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0440 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_431 A) from (by
          unfold nb090_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_432 A) from (by
            unfold nb090_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0441 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_433 h) from (by
          unfold nb090_alpha_dummy_433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_434 h) from (by
            unfold nb090_alpha_dummy_434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0442 (A : Class) :
    (nb090_alpha_dummy_432 A) ∈ (((Class.cv (nb090_alpha_dummy_432 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0443 (h : Var) :
    (nb090_alpha_dummy_434 h) ∈ (((Class.cv (nb090_alpha_dummy_434 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0444 (A : Class) :
    (nb090_alpha_dummy_439 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_439 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0445 (h : Var) :
    (nb090_alpha_dummy_441 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_441 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0446 (A : Class) :
    (nb090_alpha_dummy_439 A) ∈
      (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0447 (h : Var) :
    (nb090_alpha_dummy_441 h) ∈
      (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0448 (A : Class) :
    (nb090_alpha_dummy_446 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0449 (h : Var) :
    (nb090_alpha_dummy_449 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0450 (A : Class) :
    (nb090_alpha_dummy_446 A) ∈
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0451 (h : Var) :
    (nb090_alpha_dummy_449 h) ∈
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0452 (A : Class) :
    (nb090_alpha_dummy_447 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
            (Class.cv (nb090_alpha_dummy_447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0453 (h : Var) :
    (nb090_alpha_dummy_450 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
            (Class.cv (nb090_alpha_dummy_450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0454 (A : Class) :
    (nb090_alpha_dummy_447 A) ∈
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0455 (h : Var) :
    (nb090_alpha_dummy_450 h) ∈
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0456 (A : Class) :
    (nb090_alpha_dummy_446 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0457 (h : Var) :
    (nb090_alpha_dummy_449 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0458 (A : Class) :
    (nb090_alpha_dummy_446 A) ∈
      (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0459 (h : Var) :
    (nb090_alpha_dummy_449 h) ∈
      (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0460 (A : Class) :
    (nb090_alpha_dummy_447 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0461 (h : Var) :
    (nb090_alpha_dummy_450 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0462 (A : Class) :
    (nb090_alpha_dummy_447 A) ∈
      (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0463 (h : Var) :
    (nb090_alpha_dummy_450 h) ∈
      (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0464 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0465 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_431 A) from (by
          unfold nb090_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_432 A) from (by
            unfold nb090_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0466 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0467 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_433 h) from (by
          unfold nb090_alpha_dummy_433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_434 h) from (by
            unfold nb090_alpha_dummy_434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0468 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_431 A) from (by
          unfold nb090_alpha_dummy_431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_432 A) from (by
            unfold nb090_alpha_dummy_432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0469 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_433 h) from (by
          unfold nb090_alpha_dummy_433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_434 h) from (by
            unfold nb090_alpha_dummy_434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0470 (A : Class) :
    (nb090_alpha_dummy_432 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0471 (h : Var) :
    (nb090_alpha_dummy_434 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0472 (A : Class) :
    (nb090_alpha_dummy_432 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0473 (h : Var) :
    (nb090_alpha_dummy_434 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0474 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0475 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_467 A) from (by
          unfold nb090_alpha_dummy_467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_468 A) from (by
            unfold nb090_alpha_dummy_468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0476 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0477 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_469 h) from (by
          unfold nb090_alpha_dummy_469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_470 h) from (by
            unfold nb090_alpha_dummy_470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0478 (A : Class) :
    (nb090_alpha_dummy_423 A) ∈
      (((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_467 A) from (by
          unfold nb090_alpha_dummy_467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_468 A) from (by
            unfold nb090_alpha_dummy_468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0479 (h : Var) :
    (nb090_alpha_dummy_426 h) ∈
      (((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_469 h) from (by
          unfold nb090_alpha_dummy_469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_470 h) from (by
            unfold nb090_alpha_dummy_470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0480 (A : Class) :
    (nb090_alpha_dummy_468 A) ∈ (((Class.cv (nb090_alpha_dummy_468 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0481 (h : Var) :
    (nb090_alpha_dummy_470 h) ∈ (((Class.cv (nb090_alpha_dummy_470 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0482 (A : Class) :
    (nb090_alpha_dummy_475 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_475 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0483 (h : Var) :
    (nb090_alpha_dummy_477 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_477 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0484 (A : Class) :
    (nb090_alpha_dummy_475 A) ∈
      (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0485 (h : Var) :
    (nb090_alpha_dummy_477 h) ∈
      (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0486 (A : Class) :
    (nb090_alpha_dummy_482 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0487 (h : Var) :
    (nb090_alpha_dummy_485 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0488 (A : Class) :
    (nb090_alpha_dummy_482 A) ∈
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0489 (h : Var) :
    (nb090_alpha_dummy_485 h) ∈
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0490 (A : Class) :
    (nb090_alpha_dummy_483 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
            (Class.cv (nb090_alpha_dummy_483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0491 (h : Var) :
    (nb090_alpha_dummy_486 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
            (Class.cv (nb090_alpha_dummy_486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0492 (A : Class) :
    (nb090_alpha_dummy_483 A) ∈
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0493 (h : Var) :
    (nb090_alpha_dummy_486 h) ∈
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0494 (A : Class) :
    (nb090_alpha_dummy_482 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0495 (h : Var) :
    (nb090_alpha_dummy_485 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0496 (A : Class) :
    (nb090_alpha_dummy_482 A) ∈
      (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part019`. -/


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

theorem nb090_support_mem_0497 (h : Var) :
    (nb090_alpha_dummy_485 h) ∈
      (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0498 (A : Class) :
    (nb090_alpha_dummy_483 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0499 (h : Var) :
    (nb090_alpha_dummy_486 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0500 (A : Class) :
    (nb090_alpha_dummy_483 A) ∈
      (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0501 (h : Var) :
    (nb090_alpha_dummy_486 h) ∈
      (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0502 (A : Class) :
    (nb090_alpha_dummy_425 A) ∈
      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0503 (A : Class) :
    (nb090_alpha_dummy_425 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_467 A) from (by
          unfold nb090_alpha_dummy_467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_468 A) from (by
            unfold nb090_alpha_dummy_468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0504 (h : Var) :
    (nb090_alpha_dummy_428 h) ∈
      (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0505 (h : Var) :
    (nb090_alpha_dummy_428 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_469 h) from (by
          unfold nb090_alpha_dummy_469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_470 h) from (by
            unfold nb090_alpha_dummy_470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0506 (A : Class) :
    (nb090_alpha_dummy_425 A) ∈
      (((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_467 A) from (by
          unfold nb090_alpha_dummy_467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_468 A) from (by
            unfold nb090_alpha_dummy_468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0507 (h : Var) :
    (nb090_alpha_dummy_428 h) ∈
      (((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_469 h) from (by
          unfold nb090_alpha_dummy_469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_470 h) from (by
            unfold nb090_alpha_dummy_470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0508 (A : Class) :
    (nb090_alpha_dummy_468 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0509 (h : Var) :
    (nb090_alpha_dummy_470 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0510 (A : Class) :
    (nb090_alpha_dummy_468 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0511 (h : Var) :
    (nb090_alpha_dummy_470 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0512 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (Class.cv (nb090_alpha_dummy_503 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0513 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb090_alpha_dummy_505 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0514 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (Class.cv (nb090_alpha_dummy_503 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0515 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb090_alpha_dummy_505 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0516 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0517 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_509 A) from (by
          unfold nb090_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_510 A) from (by
            unfold nb090_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0518 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0519 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_511 h) from (by
          unfold nb090_alpha_dummy_511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_512 h) from (by
            unfold nb090_alpha_dummy_512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0520 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_509 A) from (by
          unfold nb090_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_510 A) from (by
            unfold nb090_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0521 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_511 h) from (by
          unfold nb090_alpha_dummy_511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_512 h) from (by
            unfold nb090_alpha_dummy_512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0522 (A : Class) :
    (nb090_alpha_dummy_510 A) ∈ (((Class.cv (nb090_alpha_dummy_510 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0523 (h : Var) :
    (nb090_alpha_dummy_512 h) ∈ (((Class.cv (nb090_alpha_dummy_512 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0524 (A : Class) :
    (nb090_alpha_dummy_517 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_517 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0525 (h : Var) :
    (nb090_alpha_dummy_519 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_519 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0526 (A : Class) :
    (nb090_alpha_dummy_517 A) ∈
      (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0527 (h : Var) :
    (nb090_alpha_dummy_519 h) ∈
      (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0528 (A : Class) :
    (nb090_alpha_dummy_524 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0529 (h : Var) :
    (nb090_alpha_dummy_527 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0530 (A : Class) :
    (nb090_alpha_dummy_524 A) ∈
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0531 (h : Var) :
    (nb090_alpha_dummy_527 h) ∈
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0532 (A : Class) :
    (nb090_alpha_dummy_525 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
            (Class.cv (nb090_alpha_dummy_525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0533 (h : Var) :
    (nb090_alpha_dummy_528 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
            (Class.cv (nb090_alpha_dummy_528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0534 (A : Class) :
    (nb090_alpha_dummy_525 A) ∈
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0535 (h : Var) :
    (nb090_alpha_dummy_528 h) ∈
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0536 (A : Class) :
    (nb090_alpha_dummy_524 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0537 (h : Var) :
    (nb090_alpha_dummy_527 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0538 (A : Class) :
    (nb090_alpha_dummy_524 A) ∈
      (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0539 (h : Var) :
    (nb090_alpha_dummy_527 h) ∈
      (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0540 (A : Class) :
    (nb090_alpha_dummy_525 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0541 (h : Var) :
    (nb090_alpha_dummy_528 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0542 (A : Class) :
    (nb090_alpha_dummy_525 A) ∈
      (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0543 (h : Var) :
    (nb090_alpha_dummy_528 h) ∈
      (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0544 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0545 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_509 A) from (by
          unfold nb090_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_510 A) from (by
            unfold nb090_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0546 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0547 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_511 h) from (by
          unfold nb090_alpha_dummy_511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_512 h) from (by
            unfold nb090_alpha_dummy_512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0548 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_509 A) from (by
          unfold nb090_alpha_dummy_509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_510 A) from (by
            unfold nb090_alpha_dummy_510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0549 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_511 h) from (by
          unfold nb090_alpha_dummy_511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_512 h) from (by
            unfold nb090_alpha_dummy_512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0550 (A : Class) :
    (nb090_alpha_dummy_510 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0551 (h : Var) :
    (nb090_alpha_dummy_512 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0552 (A : Class) :
    (nb090_alpha_dummy_510 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0553 (h : Var) :
    (nb090_alpha_dummy_512 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0554 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0555 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_545 A) from (by
          unfold nb090_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_546 A) from (by
            unfold nb090_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0556 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0557 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_547 h) from (by
          unfold nb090_alpha_dummy_547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_548 h) from (by
            unfold nb090_alpha_dummy_548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0558 (A : Class) :
    (nb090_alpha_dummy_504 A) ∈
      (((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_545 A) from (by
          unfold nb090_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_546 A) from (by
            unfold nb090_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0559 (h : Var) :
    (nb090_alpha_dummy_506 h) ∈
      (((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_547 h) from (by
          unfold nb090_alpha_dummy_547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_548 h) from (by
            unfold nb090_alpha_dummy_548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0560 (A : Class) :
    (nb090_alpha_dummy_546 A) ∈ (((Class.cv (nb090_alpha_dummy_546 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0561 (h : Var) :
    (nb090_alpha_dummy_548 h) ∈ (((Class.cv (nb090_alpha_dummy_548 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0562 (A : Class) :
    (nb090_alpha_dummy_553 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_553 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0563 (h : Var) :
    (nb090_alpha_dummy_555 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_555 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0564 (A : Class) :
    (nb090_alpha_dummy_553 A) ∈
      (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0565 (h : Var) :
    (nb090_alpha_dummy_555 h) ∈
      (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0566 (A : Class) :
    (nb090_alpha_dummy_560 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0567 (h : Var) :
    (nb090_alpha_dummy_563 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0568 (A : Class) :
    (nb090_alpha_dummy_560 A) ∈
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0569 (h : Var) :
    (nb090_alpha_dummy_563 h) ∈
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0570 (A : Class) :
    (nb090_alpha_dummy_561 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
            (Class.cv (nb090_alpha_dummy_561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0571 (h : Var) :
    (nb090_alpha_dummy_564 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
            (Class.cv (nb090_alpha_dummy_564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0572 (A : Class) :
    (nb090_alpha_dummy_561 A) ∈
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0573 (h : Var) :
    (nb090_alpha_dummy_564 h) ∈
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0574 (A : Class) :
    (nb090_alpha_dummy_560 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0575 (h : Var) :
    (nb090_alpha_dummy_563 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0576 (A : Class) :
    (nb090_alpha_dummy_560 A) ∈
      (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0577 (h : Var) :
    (nb090_alpha_dummy_563 h) ∈
      (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0578 (A : Class) :
    (nb090_alpha_dummy_561 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0579 (h : Var) :
    (nb090_alpha_dummy_564 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0580 (A : Class) :
    (nb090_alpha_dummy_561 A) ∈
      (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0581 (h : Var) :
    (nb090_alpha_dummy_564 h) ∈
      (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0582 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0583 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_545 A) from (by
          unfold nb090_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_546 A) from (by
            unfold nb090_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0584 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0585 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_547 h) from (by
          unfold nb090_alpha_dummy_547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_548 h) from (by
            unfold nb090_alpha_dummy_548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0586 (A : Class) :
    (nb090_alpha_dummy_503 A) ∈
      (((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_545 A) from (by
          unfold nb090_alpha_dummy_545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_546 A) from (by
            unfold nb090_alpha_dummy_546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0587 (h : Var) :
    (nb090_alpha_dummy_505 h) ∈
      (((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_547 h) from (by
          unfold nb090_alpha_dummy_547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_548 h) from (by
            unfold nb090_alpha_dummy_548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0588 (A : Class) :
    (nb090_alpha_dummy_546 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0589 (h : Var) :
    (nb090_alpha_dummy_548 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0590 (A : Class) :
    (nb090_alpha_dummy_546 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0591 (h : Var) :
    (nb090_alpha_dummy_548 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0592 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0593 (h : Var) :
    h ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0594 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0595 (h : Var) :
    h ∈
      (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
        ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0596 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0597 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
                (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
                (Class.cv (nb090_alpha_dummy_425 A)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
                (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
                (Class.cv (nb090_alpha_dummy_424 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_425 A) from (by
          unfold nb090_alpha_dummy_425;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0596 A) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0598 (h : Var) :
    h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0599 (h : Var) :
    h ∈
      (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪
        ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa
              (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
              (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb090_alpha_dummy_427 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_428 h) from (by
          unfold nb090_alpha_dummy_428;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0598 h) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0600 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (Class.cv (nb090_alpha_dummy_503 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0601 (h : Var) :
    h ∈
      (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb090_alpha_dummy_505 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0602 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0603 (h : Var) : h ∈ (((syn_ccnv (Class.cv h))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0604 (A : Class) :
    (nb090_alpha_dummy_425 A) ∈
      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0605 (A : Class) :
    (nb090_alpha_dummy_425 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_581 A) from (by
          unfold nb090_alpha_dummy_581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_582 A) from (by
            unfold nb090_alpha_dummy_582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0606 (h : Var) :
    (nb090_alpha_dummy_428 h) ∈
      (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0607 (h : Var) :
    (nb090_alpha_dummy_428 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_583 h) from (by
          unfold nb090_alpha_dummy_583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_584 h) from (by
            unfold nb090_alpha_dummy_584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0608 (A : Class) :
    (nb090_alpha_dummy_425 A) ∈
      (((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_581 A) from (by
          unfold nb090_alpha_dummy_581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_425 A) ≠ (nb090_alpha_dummy_582 A) from (by
            unfold nb090_alpha_dummy_582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0609 (h : Var) :
    (nb090_alpha_dummy_428 h) ∈
      (((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_583 h) from (by
          unfold nb090_alpha_dummy_583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_428 h) ≠ (nb090_alpha_dummy_584 h) from (by
            unfold nb090_alpha_dummy_584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0610 (A : Class) :
    (nb090_alpha_dummy_582 A) ∈ (((Class.cv (nb090_alpha_dummy_582 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0611 (h : Var) :
    (nb090_alpha_dummy_584 h) ∈ (((Class.cv (nb090_alpha_dummy_584 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0612 (A : Class) :
    (nb090_alpha_dummy_589 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_589 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0613 (h : Var) :
    (nb090_alpha_dummy_591 h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_591 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0614 (A : Class) :
    (nb090_alpha_dummy_589 A) ∈
      (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0615 (h : Var) :
    (nb090_alpha_dummy_591 h) ∈
      (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0616 (A : Class) :
    (nb090_alpha_dummy_596 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0617 (h : Var) :
    (nb090_alpha_dummy_599 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0618 (A : Class) :
    (nb090_alpha_dummy_596 A) ∈
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0619 (h : Var) :
    (nb090_alpha_dummy_599 h) ∈
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0620 (A : Class) :
    (nb090_alpha_dummy_597 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
            (Class.cv (nb090_alpha_dummy_597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0621 (h : Var) :
    (nb090_alpha_dummy_600 h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
            (Class.cv (nb090_alpha_dummy_600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0622 (A : Class) :
    (nb090_alpha_dummy_597 A) ∈
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0623 (h : Var) :
    (nb090_alpha_dummy_600 h) ∈
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0624 (A : Class) :
    (nb090_alpha_dummy_596 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0625 (h : Var) :
    (nb090_alpha_dummy_599 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0626 (A : Class) :
    (nb090_alpha_dummy_596 A) ∈
      (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0627 (h : Var) :
    (nb090_alpha_dummy_599 h) ∈
      (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0628 (A : Class) :
    (nb090_alpha_dummy_597 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0629 (h : Var) :
    (nb090_alpha_dummy_600 h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0630 (A : Class) :
    (nb090_alpha_dummy_597 A) ∈
      (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0631 (h : Var) :
    (nb090_alpha_dummy_600 h) ∈
      (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0632 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0633 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_581 A)
              (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_581 A) from (by
          unfold nb090_alpha_dummy_581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_582 A) from (by
            unfold nb090_alpha_dummy_582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0634 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
