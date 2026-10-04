/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelrescnvfunndv`. -/
@[expose]
noncomputable def gWppqkrelrescnvfunndv (A : Class) (B : Class)
    (_hyp_wppqkrelrescnvfunndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (_hyp_wppqkrelrescnvfunndv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWfun (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let d : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  let v : Var := freshVar proofSupport 6
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_d_ne_s : d ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_t : d ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_u : d ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_d : u ≠ d := Ne.symm fresh_d_ne_u
  have fresh_d_ne_a : d ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_d : a ≠ d := Ne.symm fresh_d_ne_a
  have fresh_d_ne_b : d ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_d : b ≠ d := Ne.symm fresh_d_ne_b
  have fresh_d_ne_v : d ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_v_ne_d : v ≠ d := Ne.symm fresh_d_ne_v
  have fresh_s_ne_t : s ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_u : s ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_s : u ≠ s := Ne.symm fresh_s_ne_u
  have fresh_s_ne_a : s ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_s : a ≠ s := Ne.symm fresh_s_ne_a
  have fresh_s_ne_b : s ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_s : b ≠ s := Ne.symm fresh_s_ne_b
  have fresh_s_ne_v : s ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_v_ne_s : v ≠ s := Ne.symm fresh_s_ne_v
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have fresh_t_ne_a : t ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_t_ne_v : t ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_v_ne_t : v ≠ t := Ne.symm fresh_t_ne_v
  have fresh_u_ne_a : u ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_u : a ≠ u := Ne.symm fresh_u_ne_a
  have fresh_u_ne_b : u ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_u : b ≠ u := Ne.symm fresh_u_ne_b
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_v : a ≠ v :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_v_ne_a : v ≠ a := Ne.symm fresh_a_ne_v
  have fresh_b_ne_v : b ≠ v :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_v_ne_b : v ≠ b := Ne.symm fresh_b_ne_v
  have dv_cache_0001 : u ∉ ((Class.cv s)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_s, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_u_not_A, fresh_u_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_u, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_u, not_false_eq_true])
  have dv_cache_0005 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0006 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0007 : a ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_B, not_false_eq_true])
  have dv_cache_0008 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0009 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 :
    a ∉
      ((synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B)))
          (.classEq (.cv s) (synCsn (synCsn (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_d, fresh_a_ne_s, fresh_a_not_A, fresh_a_not_B,
          fresh_a_ne_t, fresh_a_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Wff.classEq (.cv s) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_s, fresh_a_ne_t, or_false, not_false_eq_true])
  have dv_cache_0012 :
    b ∉
      ((synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B)))
          (.classEq (.cv s) (synCsn (synCsn (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_s, fresh_b_not_A, fresh_b_not_B,
          fresh_b_ne_t, fresh_b_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.classEq (.cv s) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_s, fresh_b_ne_t, or_false, not_false_eq_true])
  have dv_cache_0014 : v ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_t, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_v_not_A, fresh_v_not_B, or_false, not_false_eq_true])
  have dv_cache_0016 : v ∉ ((Wff.classEq (.cv s) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_s, fresh_v_ne_t, or_false, not_false_eq_true])
  have dv_cache_0017 :
    v ∉
      ((synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
              (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
          (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_d, fresh_v_ne_s, fresh_v_not_A, fresh_v_not_B,
          fresh_v_ne_t, fresh_v_ne_u, fresh_v_ne_a, fresh_v_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : u ∉ ((Wff.classEq (.cv s) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_s, fresh_u_ne_t, or_false, not_false_eq_true])
  have dv_cache_0019 :
    u ∉
      ((synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
              (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
            (.cv t)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_d, fresh_u_ne_s, fresh_u_not_A, fresh_u_not_B,
          fresh_u_ne_t, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    d ∉
      ((synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_d_not_A, fresh_d_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0021 :
    s ∉
      ((synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_s_not_A, fresh_s_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 :
    t ∉
      ((synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0023 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0024 : d ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show d ≠ t from (by exact fresh_d_ne_t))
  have dv_cache_0025 : s ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show s ≠ t from (by exact fresh_s_ne_t))
  have p0000 :=
    @gSimpl
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv s))
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv t))
  have p0001 :=
    @gBrcnv (.cv d) (.cv s)
      (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
  have p0002 :=
    @gBrres (.cv s) (.cv d) (synCkqrel (synCwppqkrelkernel))
      (synCpw1 (synCpw1 (synCxp A B)))
  have p0003 :=
    @gBitri
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv s))
      (synWbr (.cv s)
        (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
        (.cv d))
      (synWa (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))))
      p0001 p0002
  have p0004 :=
    @gBiimpi
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv s))
      (synWa (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))))
      p0003
  have p0005 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv s))
      (synWa (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))))
      p0000 p0004
  have p0006 :=
    @gSimpr (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
  have p0007 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWa (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))))
      (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))) p0005 p0006
  have p0008 := @gElpw12 u (.cv s) (synCxp A B) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @gBiimpi (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (synWrex u (synCxp A B) (.classEq (.cv s) (synCsn (synCsn (.cv u))))) p0008
  have p0010 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (synWrex u (synCxp A B) (.classEq (.cv s) (synCsn (synCsn (.cv u))))) p0007
      p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
              (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
            (.cv t))) (.classMem (.cv u) (synCxp A B)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u))))
  have p0012 :=
    @gSimpr
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (.classMem (.cv u) (synCxp A B))
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
              (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
            (.cv t))) (.classMem (.cv u) (synCxp A B)))
      (.classMem (.cv u) (synCxp A B)) p0011 p0012
  have p0014 :=
    @gElxp a b (.cv u) A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0015 :=
    @gBiimpi (.classMem (.cv u) (synCxp A B))
      (synWex a (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (.classMem (.cv u) (synCxp A B))
      (synWex a (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0013 p0015
  have p0017 :=
    @gNfv
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      a dv_cache_0010
  have p0018 := @gNfv (.classEq (.cv s) (.cv t)) a dv_cache_0011
  have p0019 :=
    @gNfv
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      b dv_cache_0012
  have p0020 := @gNfv (.classEq (.cv s) (.cv t)) b dv_cache_0013
  have p0021 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0023 :=
    @gSimpl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (.classMem (.cv u) (synCxp A B))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
              (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
            (.cv t))) (.classMem (.cv u) (synCxp A B)))
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      p0011 p0023
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      p0021 p0024
  have p0026 :=
    @gSimpr
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv s))
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv t))
  have p0027 :=
    @gBrcnv (.cv d) (.cv t)
      (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
  have p0028 :=
    @gBrres (.cv t) (.cv d) (synCkqrel (synCwppqkrelkernel))
      (synCpw1 (synCpw1 (synCxp A B)))
  have p0029 :=
    @gBitri
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv t))
      (synWbr (.cv t)
        (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
        (.cv d))
      (synWa (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))))
      p0027 p0028
  have p0030 :=
    @gBiimpi
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv t))
      (synWa (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))))
      p0029
  have p0031 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (.cv t))
      (synWa (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))))
      p0026 p0030
  have p0032 :=
    @gSimpr (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B))))
  have p0033 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWa (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))))
      (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))) p0031 p0032
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))) p0025 p0033
  have p0035 := @gElpw12 v (.cv t) (synCxp A B) dv_cache_0014 dv_cache_0015
  have p0036 :=
    @gBiimpi (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B))))
      (synWrex v (synCxp A B) (.classEq (.cv t) (synCsn (synCsn (.cv v))))) p0035
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B))))
      (synWrex v (synCxp A B) (.classEq (.cv t) (synCsn (synCsn (.cv v))))) p0034
      p0036
  have p0038 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
              (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
          (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (synCxp A B)))
      (.classEq (.cv t) (synCsn (synCsn (.cv v))))
  have p0039 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (.cv v) (synCxp A B))
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
              (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
          (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (synCxp A B)))
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      p0038 p0039
  have p0042 :=
    @gSimpr
      (synWa (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
              (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
            (.cv t))) (.classMem (.cv u) (synCxp A B)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u))))
  have p0043 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (.classEq (.cv s) (synCsn (synCsn (.cv u)))) p0021 p0042
  have p0044 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0045 :=
    @gSimpl (.classEq (.cv u) (synCop (.cv a) (.cv b)))
      (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv u) (synCop (.cv a) (.cv b))) p0044 p0045
  have p0047 := @gSneq (.cv u) (synCop (.cv a) (.cv b))
  have p0048 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv u) (synCop (.cv a) (.cv b)))
      (.classEq (synCsn (.cv u)) (synCsn (synCop (.cv a) (.cv b)))) p0046 p0047
  have p0049 :=
    @gSneqd
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synCsn (.cv u)) (synCsn (synCop (.cv a) (.cv b))) p0048
  have p0050 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (synCsn (synCsn (.cv u))) (synCsn (synCsn (synCop (.cv a) (.cv b))))
      p0043 p0049
  have p0051 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv s) (synCsn (synCsn (synCop (.cv a) (.cv b))))) p0040 p0050
  have p0052 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
              (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
          (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (synCxp A B)))
      (.classEq (.cv t) (synCsn (synCsn (.cv v))))
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      p0040 p0025
  have p0068 :=
    @gSimpl (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B))))
  have p0069 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWa (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (synCpw1 (synCpw1 (synCxp A B)))))
      (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d)) p0031 p0068
  have p0070 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d)) p0061 p0069
  have p0071 :=
    (Nominal.biimpRefl (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d)))
  have p0072 :=
    @gBiimpi (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (synCop (.cv t) (.cv d)) (synCkqrel (synCwppqkrelkernel))) p0071
  have p0073 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synWbr (.cv t) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (synCop (.cv t) (.cv d)) (synCkqrel (synCwppqkrelkernel))) p0070 p0072
  have p0075 :=
    @gOpeq1d
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.cv t) (synCsn (synCsn (.cv v))) (.cv d) p0052
  have p0076 :=
    @gEleq1d
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synCop (.cv t) (.cv d)) (synCop (synCsn (synCsn (.cv v))) (.cv d))
      (synCkqrel (synCwppqkrelkernel)) p0075
  have p0077 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.classMem (synCop (.cv t) (.cv d)) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCop (synCsn (synCsn (.cv v))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      p0073 p0076
  have p0092 :=
    @gSimpl (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
  have p0093 :=
    @gSyl
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWa (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))))
      (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d)) p0005 p0092
  have p0094 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d)) p0025 p0093
  have p0095 :=
    (Nominal.biimpRefl (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d)))
  have p0096 :=
    @gBiimpi (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))) p0095
  have p0097 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))) p0094 p0096
  have p0108 :=
    @gOpeq1d
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d) p0050
  have p0109 :=
    @gEleq1d
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synCop (.cv s) (.cv d))
      (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
      (synCkqrel (synCwppqkrelkernel)) p0108
  have p0110 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      p0097 p0109
  have p0111 := @gVex a
  have p0112 := @gVex b
  have p0113 := @gVex d
  have p0114 := @gWppqkrelcanonicalfiberndv (.cv a) (.cv b) (.cv d) p0111 p0112 p0113
  have p0115 :=
    @gBiimpi
      (.classMem (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (.cv d) (synCopk (.cv a) (.cv b))) p0114
  have p0116 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (.cv d) (synCopk (.cv a) (.cv b))) p0110 p0115
  have p0117 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv d) (synCopk (.cv a) (.cv b))) p0040 p0116
  have p0118 :=
    @gOpeq2d
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.cv d) (synCopk (.cv a) (.cv b)) (synCsn (synCsn (.cv v))) p0117
  have p0119 :=
    @gEleq1d
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synCop (synCsn (synCsn (.cv v))) (.cv d))
      (synCop (synCsn (synCsn (.cv v))) (synCopk (.cv a) (.cv b)))
      (synCkqrel (synCwppqkrelkernel)) p0118
  have p0120 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.classMem (synCop (synCsn (synCsn (.cv v))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCop (synCsn (synCsn (.cv v))) (synCopk (.cv a) (.cv b)))
        (synCkqrel (synCwppqkrelkernel)))
      p0077 p0119
  have p0121 := @gVex v
  have p0124 := @gWppqkrelkernelpointbrndv (.cv v) (.cv a) (.cv b) p0121 p0111 p0112
  have p0125 :=
    @gBiimpi
      (.classMem (synCop (synCsn (synCsn (.cv v))) (synCopk (.cv a) (.cv b)))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (.cv v) (synCop (.cv a) (.cv b))) p0124
  have p0126 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.classMem (synCop (synCsn (synCsn (.cv v))) (synCopk (.cv a) (.cv b)))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (.cv v) (synCop (.cv a) (.cv b))) p0120 p0125
  have p0127 :=
    @gSneqd
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.cv v) (synCop (.cv a) (.cv b)) p0126
  have p0128 :=
    @gSneqd
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (synCsn (.cv v)) (synCsn (synCop (.cv a) (.cv b))) p0127
  have p0129 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.cv t) (synCsn (synCsn (.cv v))) (synCsn (synCsn (synCop (.cv a) (.cv b))))
      p0052 p0128
  have p0130 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.cv t) (synCsn (synCsn (synCop (.cv a) (.cv b)))) p0129
  have p0131 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                      (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classMem (.cv u) (synCxp A B)))
              (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
            (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (synCxp A B))) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.cv s) (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv t) p0051 p0130
  have p0132 :=
    @gEx
      (synWa (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
              (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
          (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (synCxp A B)))
      (.classEq (.cv t) (synCsn (synCsn (.cv v)))) (.classEq (.cv s) (.cv t)) p0131
  have p0133 :=
    @gRexlimdva
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv t) (synCsn (synCsn (.cv v)))) (.classEq (.cv s) (.cv t)) v
      (synCxp A B) dv_cache_0016 dv_cache_0017 p0132
  have p0134 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                  (synCres (synCkqrel (synCwppqkrelkernel))
                    (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWrex v (synCxp A B) (.classEq (.cv t) (synCsn (synCsn (.cv v)))))
      (.classEq (.cv s) (.cv t)) p0037 p0133
  have p0135 :=
    @gEx
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv s) (.cv t)) p0134
  have p0136 :=
    @gExlimd
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv s) (.cv t)) b p0019 p0020 p0135
  have p0137 :=
    @gExlimd
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv s) (.cv t)) a p0017 p0018 p0136
  have p0138 :=
    @gMpd
      (synWa (synWa (synWa (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                (synCres (synCkqrel (synCwppqkrelkernel))
                  (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWex a (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      (.classEq (.cv s) (.cv t)) p0016 p0137
  have p0139 :=
    @gEx
      (synWa (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
              (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
            (.cv t))) (.classMem (.cv u) (synCxp A B)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u)))) (.classEq (.cv s) (.cv t)) p0138
  have p0140 :=
    @gRexlimdva
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u)))) (.classEq (.cv s) (.cv t)) u
      (synCxp A B) dv_cache_0018 dv_cache_0019 p0139
  have p0141 :=
    @gMpd
      (synWa (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (.cv t)))
      (synWrex u (synCxp A B) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (.classEq (.cv s) (.cv t)) p0010 p0140
  have p0142 := Nominal.gen p0141 t
  have p0143 := Nominal.gen p0142 s
  have p0144 := Nominal.gen p0143 d
  have p0145 :=
    @gDffun2 d s t
      (synCcnv
        (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
  have p0146_e01_recanon :
    Nominal.NPrf
      (synWb (synWfun (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B)))))) (.all d (.all s (.all t (.imp (synWa
                  (synWbr (.cv d) (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d)
                    (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
                        (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
                (.classEq (.cv s) (.cv t))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWfun synWss synCin synCcompl synCnin synWnan synWa
          synCcom synCopab synWex synCcnv synCid
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0145
  have p0146 :=
    @gMpbir
      (synWfun (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))))
      (.all d (.all s (.all t (.imp (synWa (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv s)) (synWbr (.cv d) (synCcnv
                    (synCres (synCkqrel (synCwppqkrelkernel))
                      (synCpw1 (synCpw1 (synCxp A B))))) (.cv t)))
              (.classEq (.cv s) (.cv t))))))
      p0144 p0146_e01_recanon
  exact p0146


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelrestypedenqkndv`. -/
@[expose]
noncomputable def gWppqkrelrestypedenqkndv (A : Class) (B : Class)
    (hyp_wppqkrelresf1oqkndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppqkrelresf1oqkndv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWbr (synCpw1 (synCpw1 (synCxp A B))) (synCen) (synCqkrel (synCxp A B))) :=
  by
  have p0000 :=
    @gWppqkrelresfnndv A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0001 :=
    @gWppqkrelrescnvfunndv A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0002 := @gWppqkrelresrangevalndv (synCxp A B)
  have p0003 :=
    @gN3pm32i
      (synWfn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
        (synCpw1 (synCpw1 (synCxp A B))))
      (synWfun (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))))
      (.classEq (synCrn (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B))))) (synCqkrel (synCxp A B)))
      p0000 p0001 p0002
  have p0004 :=
    @gDff1o2 (synCpw1 (synCpw1 (synCxp A B))) (synCqkrel (synCxp A B))
      (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
  have p0005 :=
    @gMpbir
      (synWf1o
        (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
        (synCpw1 (synCpw1 (synCxp A B))) (synCqkrel (synCxp A B)))
      (synW3a (synWfn (synCres (synCkqrel (synCwppqkrelkernel))
            (synCpw1 (synCpw1 (synCxp A B)))) (synCpw1 (synCpw1 (synCxp A B)))) (synWfun
          (synCcnv (synCres (synCkqrel (synCwppqkrelkernel))
              (synCpw1 (synCpw1 (synCxp A B)))))) (.classEq (synCrn
            (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B)))))
          (synCqkrel (synCxp A B))))
      p0003 p0004
  have p0006 := @gWppqkrelkernelexndv
  have p0007 := @gKqrelex (synCwppqkrelkernel) p0006
  have p0008 := @gXpex A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0009 := @gPw1ex (synCxp A B) p0008
  have p0010 := @gPw1ex (synCpw1 (synCxp A B)) p0009
  have p0011 :=
    @gResex (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))) p0007
      p0010
  have p0012 :=
    @gF1oen (synCpw1 (synCpw1 (synCxp A B))) (synCqkrel (synCxp A B))
      (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
      p0011
  have p0013 := Nominal.mp p0005 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelxprebasendv`. -/
@[expose]
noncomputable def gWppqkrelxprebasendv (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCqkrel (synCxp A B)) (synCxpk A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((synCxp A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0010 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0011 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0012 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((synCqkrel (synCxp A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((synCxpk A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQkrel x y z
      (synCxp A B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @gEleq2i (synCqkrel (synCxp A B))
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.classMem (synCop (.cv x) (.cv y)) (synCxp A B))))))
      (.cv z) p0000
  have p0002 :=
    @gAbid
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (.classMem (synCop (.cv x) (.cv y)) (synCxp A B)))))
      z
  have p0003 :=
    @gBitri (.classMem (.cv z) (synCqkrel (synCxp A B)))
      (.classMem (.cv z) (.cab z (synWex x (synWex y
              (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
                (.classMem (synCop (.cv x) (.cv y)) (synCxp A B)))))))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (.classMem (synCop (.cv x) (.cv y)) (synCxp A B)))))
      p0001 p0002
  have p0004 := @gOpelxp (.cv x) (.cv y) A B
  have p0005 :=
    @gAnbi2i (.classMem (synCop (.cv x) (.cv y)) (synCxp A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (.classEq (.cv z) (synCopk (.cv x) (.cv y))) p0004
  have p0006 :=
    @gN2exbii
      (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
        (.classMem (synCop (.cv x) (.cv y)) (synCxp A B)))
      (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      x y p0005
  have p0007 :=
    @gBitri (.classMem (.cv z) (synCqkrel (synCxp A B)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (.classMem (synCop (.cv x) (.cv y)) (synCxp A B)))))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      p0003 p0006
  have p0008 :=
    @gElxpk x y (.cv z) A B dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0004
  have p0009 :=
    @gBicomi (.classMem (.cv z) (synCxpk A B))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      p0008
  have p0010 :=
    @gBitri (.classMem (.cv z) (synCqkrel (synCxp A B)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      (.classMem (.cv z) (synCxpk A B)) p0007 p0009
  have p0011 :=
    @gEqriv z (synCqkrel (synCxp A B)) (synCxpk A B) dv_cache_0013 dv_cache_0014 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelrestypedenndv`. -/
@[expose]
noncomputable def gWppqkrelrestypedenndv (A : Class) (B : Class)
    (hyp_wppqkrelresf1ondv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppqkrelresf1ondv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWbr (synCpw1 (synCpw1 (synCxp A B))) (synCen) (synCxpk A B)) :=
  by
  have p0000 :=
    @gWppqkrelrestypedenqkndv A B hyp_wppqkrelresf1ondv_1 hyp_wppqkrelresf1ondv_2
  have p0001 := @gWppqkrelxprebasendv A B
  have p0002 :=
    @gBreq2i (synCqkrel (synCxp A B)) (synCxpk A B)
      (synCpw1 (synCpw1 (synCxp A B))) (synCen) p0001
  have p0003 :=
    @gMpbi
      (synWbr (synCpw1 (synCpw1 (synCxp A B))) (synCen) (synCqkrel (synCxp A B)))
      (synWbr (synCpw1 (synCpw1 (synCxp A B))) (synCen) (synCxpk A B)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hncardmonodndv`. -/
@[expose]
noncomputable def gHncardmonodndv (A : Class) (D : Class)
    (hyp_hncardmonodndv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hncardmonodndv_2 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWss D A) (synWbr (synChncard D) (synClec) (synChncard A))) :=
  by
  have p0000 := @gHncardeqdndv D (synCif (synWss D A) D (synC0))
  have p0001 :=
    @gBreq1d (.classEq D (synCif (synWss D A) D (synC0))) (synChncard D)
      (synChncard (synCif (synWss D A) D (synC0))) (synChncard A) (synClec) p0000
  have p0002 := @gIftrue (synWss D A) D (synC0)
  have p0003 := @gId (synWss D A)
  have p0004 :=
    @gEqsstrd (synWss D A) (synCif (synWss D A) D (synC0)) D A p0002 p0003
  have p0005 := @gIffalse (synWss D A) D (synC0)
  have p0006 := @gN0ss A
  have p0007 := @gA1i (synWss (synC0) A) (.neg (synWss D A)) p0006
  have p0008 :=
    @gEqsstrd (.neg (synWss D A)) (synCif (synWss D A) D (synC0)) (synC0) A p0005
      p0007
  have p0009 :=
    @gPm261i (synWss D A) (synWss (synCif (synWss D A) D (synC0)) A) p0004 p0008
  have p0010 := @gN0ex
  have p0011 :=
    @gPm32i (.classMem D (synCvv)) (.classMem (synC0) (synCvv)) hyp_hncardmonodndv_1
      p0010
  have p0012 := @gIfcl (synWss D A) D (synC0) (synCvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gHncardmono A (synCif (synWss D A) D (synC0)) p0009 p0013 hyp_hncardmonodndv_2
  have p0015 :=
    @gDedth (synWss D A) (synWbr (synChncard D) (synClec) (synChncard A))
      (synWbr (synChncard (synCif (synWss D A) D (synC0))) (synClec) (synChncard A))
      D (synC0) p0001 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_hncardf1leimpndv`. -/
@[expose]
noncomputable def gHncardf1leimpndv (A : Class) (D : Class) (F : Class)
    (hyp_hncardf1leimpndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (_hyp_hncardf1leimpndv_2 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hncardf1leimpndv_3 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWf1 F D A) (synWbr (synChncard D) (synClec) (synChncard A))) :=
  by
  have p0000 := @gF1f1orn D A F
  have p0001 := @gHncardf1oimpndv D (synCrn F) F hyp_hncardf1leimpndv_1
  have p0002 :=
    @gSyl (synWf1 F D A) (synWf1o F D (synCrn F))
      (.classEq (synChncard D) (synChncard (synCrn F))) p0000 p0001
  have p0003 := @gF1f D A F
  have p0004 := @gFrn D A F
  have p0005 := @gSyl (synWf1 F D A) (synWf F D A) (synWss (synCrn F) A) p0003 p0004
  have p0006 := @gRnex F hyp_hncardf1leimpndv_1
  have p0007 := @gHncardmonodndv A (synCrn F) p0006 hyp_hncardf1leimpndv_3
  have p0008 :=
    @gSyl (synWf1 F D A) (synWss (synCrn F) A)
      (synWbr (synChncard (synCrn F)) (synClec) (synChncard A)) p0005 p0007
  have p0009 :=
    @gEqbrtrd (synWf1 F D A) (synChncard D) (synChncard (synCrn F)) (synChncard A)
      (synClec) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hncardnclecndv`. -/
@[expose]
noncomputable def gHncardnclecndv (A : Class) (D : Class)
    (hyp_hncardnclecndv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hncardnclecndv_2 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCnc D) (synClec) (synCnc A))
        (synWbr (synChncard D) (synClec) (synChncard A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_D, not_false_eq_true])
  have dv_cache_0002 : f ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((synWbr (synChncard D) (synClec) (synChncard A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_f_not_D, fresh_f_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gNclenc D A f dv_cache_0001 dv_cache_0002 hyp_hncardnclecndv_1 hyp_hncardnclecndv_2
  have p0001 :=
    @gBiimpi (synWbr (synCnc D) (synClec) (synCnc A))
      (synWex f (synWf1 (.cv f) D A)) p0000
  have p0002 := @gVex f
  have p0003 :=
    @gHncardf1leimpndv A D (.cv f) p0002 hyp_hncardnclecndv_1 hyp_hncardnclecndv_2
  have p0004 :=
    @gExlimiv (synWf1 (.cv f) D A) (synWbr (synChncard D) (synClec) (synChncard A))
      f dv_cache_0003 p0003
  have p0005 :=
    @gSyl (synWbr (synCnc D) (synClec) (synCnc A)) (synWex f (synWf1 (.cv f) D A))
      (synWbr (synChncard D) (synClec) (synChncard A)) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnordcardnclecndv`. -/
@[expose]
noncomputable def gHnordcardnclecndv (A : Class) (D : Class)
    (hyp_hnordcardnclecndv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnordcardnclecndv_2 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCnc D) (synClec) (synCnc A))
        (synWbr (synCnc (synChnord D)) (synClec) (synCnc (synChnord A)))) :=
  by
  have p0000 := @gHncardnclecndv A D hyp_hnordcardnclecndv_1 hyp_hnordcardnclecndv_2
  have p0001 := (Nominal.classEqRefl (synChncard D))
  have p0002 := (Nominal.classEqRefl (synChncard A))
  have p0003 :=
    @gBreq12i (synChncard D) (synCnc (synChnord D)) (synChncard A)
      (synCnc (synChnord A)) (synClec) p0001 p0002
  have p0004 :=
    @gBiimpi (synWbr (synChncard D) (synClec) (synChncard A))
      (synWbr (synCnc (synChnord D)) (synClec) (synCnc (synChnord A))) p0003
  have p0005 :=
    @gSyl (synWbr (synCnc D) (synClec) (synCnc A))
      (synWbr (synChncard D) (synClec) (synChncard A))
      (synWbr (synCnc (synChnord D)) (synClec) (synCnc (synChnord A))) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelliteralenndv`. -/
@[expose]
noncomputable def gWppqkrelliteralenndv (X : Class)
    (hyp_wppqkrelliteralenndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (synWbr (synCxp (synCxpk X X) (synCnnc)) (synCen)
        (synCxp (synCpw1 (synCpw1 (synCxp X X))) (synCnnc))) :=
  by
  have p0000 :=
    @gWppqkrelrestypedenndv X X hyp_wppqkrelliteralenndv_1 hyp_wppqkrelliteralenndv_1
  have p0001 := @gEnsym (synCpw1 (synCpw1 (synCxp X X))) (synCxpk X X)
  have p0002 :=
    @gMpbi (synWbr (synCpw1 (synCpw1 (synCxp X X))) (synCen) (synCxpk X X))
      (synWbr (synCxpk X X) (synCen) (synCpw1 (synCpw1 (synCxp X X)))) p0000 p0001
  have p0003 := @gNncex
  have p0004 := @gEnrflx (synCnnc) p0003
  have p0005 :=
    @gPm32i (synWbr (synCxpk X X) (synCen) (synCpw1 (synCpw1 (synCxp X X))))
      (synWbr (synCnnc) (synCen) (synCnnc)) p0002 p0004
  have p0006 :=
    @gXpen (synCxpk X X) (synCpw1 (synCpw1 (synCxp X X))) (synCnnc) (synCnnc)
  have p0007 := Nominal.mp p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelliteralnceqndv`. -/
@[expose]
noncomputable def gWppqkrelliteralnceqndv (X : Class)
    (hyp_wppqkrelliteralnceqndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.classEq (synCnc (synCxp (synCxpk X X) (synCnnc)))
        (synCnc (synCxp (synCpw1 (synCpw1 (synCxp X X))) (synCnnc)))) :=
  by
  have p0000 := @gWppqkrelliteralenndv X hyp_wppqkrelliteralnceqndv_1
  have p0001 := @gXpkex X X hyp_wppqkrelliteralnceqndv_1 hyp_wppqkrelliteralnceqndv_1
  have p0002 := @gNncex
  have p0003 := @gXpex (synCxpk X X) (synCnnc) p0001 p0002
  have p0004 :=
    @gEqnc (synCxp (synCxpk X X) (synCnnc))
      (synCxp (synCpw1 (synCpw1 (synCxp X X))) (synCnnc)) p0003
  have p0005 :=
    @gMpbir
      (.classEq (synCnc (synCxp (synCxpk X X) (synCnnc)))
        (synCnc (synCxp (synCpw1 (synCpw1 (synCxp X X))) (synCnnc))))
      (synWbr (synCxp (synCxpk X X) (synCnnc)) (synCen)
        (synCxp (synCpw1 (synCpw1 (synCxp X X))) (synCnnc)))
      p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnordlnquoeq`. -/
@[expose]
noncomputable def gHnordlnquoeq (A : Class) (R : Class) (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_hnordlnquoeq_1 : Nominal.NPrf (.classEq (synClnker R) (synChwniso A))) :
    Nominal.NPrf (.classEq (synClnquo R (synChwcn A)) (synChnord A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnquo R (synChwcn A)))
  have p0001 := @gQseq2 (synClnker R) (synChwniso A) (synChwcn A)
  have p0002 := Nominal.mp hyp_hnordlnquoeq_1 p0001
  have p0003 :=
    @gEqtri (synClnquo R (synChwcn A)) (synCqs (synChwcn A) (synClnker R))
      (synCqs (synChwcn A) (synChwniso A)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (synChnord A))
  have p0005 := @gEqcomi (synChnord A) (synCqs (synChwcn A) (synChwniso A)) p0004
  have p0006 :=
    @gEqtri (synClnquo R (synChwcn A)) (synCqs (synChwcn A) (synChwniso A))
      (synChnord A) p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hnordwefromcmp`. -/
@[expose]
noncomputable def gHnordwefromcmp (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv)
    (hyp_hnordwefromcmp_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_hnordwefromcmp_2 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hnordwefromcmp_3 :
      Nominal.NPrf (.classMem (synCop R (synChwcn A)) (synClnpwc (synChwcn A))))
    (hyp_hnordwefromcmp_4 : Nominal.NPrf (.classEq (synClnker R) (synChwniso A))) :
    Nominal.NPrf (synWbr (synClnqord R (synChwcn A)) (synCwe) (synChnord A)) :=
  by
  have dv_cache_0001 : Disjoint ((synChwcn A)).fv (R).fv := by
    exact
      (show Disjoint ((synChwcn A)).fv (R).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn];
          exact (show Disjoint (A).fv (R).fv from (by exact dv_A_R))))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 := @gHwcnexg A
  have p0001 := Nominal.mp hyp_hnordwefromcmp_1 p0000
  have p0002 :=
    @gLnworigqordwe (synChwcn A) R dv_cache_0001 p0001 hyp_hnordwefromcmp_2
      hyp_hnordwefromcmp_3
  have p0003 := @gHnordlnquoeq A R dv_cache_0002 hyp_hnordwefromcmp_4
  have p0004 :=
    @gBreq2i (synClnquo R (synChwcn A)) (synChnord A) (synClnqord R (synChwcn A))
      (synCwe) p0003
  have p0005 :=
    @gMpbi (synWbr (synClnqord R (synChwcn A)) (synCwe) (synClnquo R (synChwcn A)))
      (synWbr (synClnqord R (synChwcn A)) (synCwe) (synChnord A)) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hncodecutfnfn`. -/
@[expose]
noncomputable def gHncodecutfnfn : Nominal.NPrf (synWfn (synChncodecutfn) (synCvv)) :=
  by
  have p0000 := @gLninteropfn
  have p0001 := @gLn1stfn
  have p0003 := @gFncovv (synC1st) (synC1st) p0001 p0001
  have p0004 := @gFncross
  have p0006 := @gLn2ndfn
  have p0008 := @gFncovv (synC2nd) (synC1st) p0006 p0001
  have p0009 := @gLnimageopfn
  have p0010 := @gImageswapfn
  have p0011 := @gFnlndifop
  have p0015 := @gIdex
  have p0016 := @gFnconstg (synCvv) (synCid) (synCvv)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCid))) (synCvv)) p0003 p0017
  have p0019 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st))
      (synCxp (synCvv) (synCsn (synCid)))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @gInidm (synCvv)
  have p0022 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0021
  have p0023 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCvv))
      p0020 p0022
  have p0024 :=
    @gFncovv (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0011 p0023
  have p0025 := (Nominal.classEqRefl (synChncodestrictfn))
  have p0026 :=
    @gFneq1i (synCvv) (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      p0025
  have p0027 :=
    @gMpbir (synWfn (synChncodestrictfn) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid))))) (synCvv))
      p0024 p0026
  have p0028 := @gFncovv (synCimage (synCswap)) (synChncodestrictfn) p0010 p0027
  have p0030 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0028 p0006
  have p0031 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synCimage (synCswap)) (synChncodestrictfn))
      (synC2nd)
  have p0032 := Nominal.mp p0030 p0031
  have p0034 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0021
  have p0035 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCvv))
      p0032 p0034
  have p0036 :=
    @gFncovv (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0009 p0035
  have p0037 := (Nominal.classEqRefl (synChncodepredfn))
  have p0038 :=
    @gFneq1i (synCvv) (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      p0037
  have p0039 :=
    @gMpbir (synWfn (synChncodepredfn) (synCvv))
      (synWfn (synCcom (synClnimageop)
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
        (synCvv))
      p0036 p0038
  have p0040 :=
    @gPm32i (synWfn (synCcom (synC2nd) (synC1st)) (synCvv))
      (synWfn (synChncodepredfn) (synCvv)) p0008 p0039
  have p0041 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC2nd) (synC1st)) (synChncodepredfn)
  have p0042 := Nominal.mp p0040 p0041
  have p0044 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0021
  have p0045 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) (synCvv))
      p0042 p0044
  have p0046 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0000 p0045
  have p0047 := (Nominal.classEqRefl (synChncodecarrierfn))
  have p0048 :=
    @gFneq1i (synCvv) (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      p0047
  have p0049 :=
    @gMpbir (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))) (synCvv))
      p0046 p0048
  have p0095 :=
    @gPm32i (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0049 p0049
  have p0096 := @gFntxp (synCvv) (synCvv) (synChncodecarrierfn) (synChncodecarrierfn)
  have p0097 := Nominal.mp p0095 p0096
  have p0099 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0021
  have p0100 :=
    @gMpbi
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) (synCvv)) p0097
      p0099
  have p0101 :=
    @gFncovv (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0004
      p0100
  have p0102 := (Nominal.classEqRefl (synChncodesquarefn))
  have p0103 :=
    @gFneq1i (synCvv) (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      p0102
  have p0104 :=
    @gMpbir (synWfn (synChncodesquarefn) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
        (synCvv))
      p0101 p0103
  have p0105 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synChncodesquarefn) (synCvv)) p0003 p0104
  have p0106 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st)) (synChncodesquarefn)
  have p0107 := Nominal.mp p0105 p0106
  have p0109 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0021
  have p0110 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) (synCvv))
      p0107 p0109
  have p0111 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0000 p0110
  have p0112 := (Nominal.classEqRefl (synChncoderelfn))
  have p0113 :=
    @gFneq1i (synCvv) (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      p0112
  have p0114 :=
    @gMpbir (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))) (synCvv))
      p0111 p0113
  have p0160 :=
    @gPm32i (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0114 p0049
  have p0161 := @gFntxp (synCvv) (synCvv) (synChncoderelfn) (synChncodecarrierfn)
  have p0162 := Nominal.mp p0160 p0161
  have p0164 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0021
  have p0165 :=
    @gMpbi
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn)) (synCvv)) p0162 p0164
  have p0166 := (Nominal.classEqRefl (synChncodecutfn))
  have p0167 :=
    @gFneq1i (synCvv) (synChncodecutfn)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0166
  have p0168 :=
    @gMpbir (synWfn (synChncodecutfn) (synCvv))
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn)) (synCvv)) p0165 p0167
  exact p0168


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecutpairfnfn`. -/
@[expose]
noncomputable def gHncodecutpairfnfn :
    Nominal.NPrf (synWfn (synChncodecutpairfn) (synCvv)) :=
  by
  have p0000 := @gLninteropfn
  have p0001 := @gLn1stfn
  have p0003 := @gFncovv (synC1st) (synC1st) p0001 p0001
  have p0004 := @gFncross
  have p0006 := @gLn2ndfn
  have p0008 := @gFncovv (synC2nd) (synC1st) p0006 p0001
  have p0009 := @gLnimageopfn
  have p0010 := @gImageswapfn
  have p0011 := @gFnlndifop
  have p0015 := @gIdex
  have p0016 := @gFnconstg (synCvv) (synCid) (synCvv)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCid))) (synCvv)) p0003 p0017
  have p0019 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st))
      (synCxp (synCvv) (synCsn (synCid)))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @gInidm (synCvv)
  have p0022 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0021
  have p0023 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCvv))
      p0020 p0022
  have p0024 :=
    @gFncovv (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0011 p0023
  have p0025 := (Nominal.classEqRefl (synChncodestrictfn))
  have p0026 :=
    @gFneq1i (synCvv) (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      p0025
  have p0027 :=
    @gMpbir (synWfn (synChncodestrictfn) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid))))) (synCvv))
      p0024 p0026
  have p0028 := @gFncovv (synCimage (synCswap)) (synChncodestrictfn) p0010 p0027
  have p0030 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0028 p0006
  have p0031 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synCimage (synCswap)) (synChncodestrictfn))
      (synC2nd)
  have p0032 := Nominal.mp p0030 p0031
  have p0034 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0021
  have p0035 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCvv))
      p0032 p0034
  have p0036 :=
    @gFncovv (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0009 p0035
  have p0037 := (Nominal.classEqRefl (synChncodepredfn))
  have p0038 :=
    @gFneq1i (synCvv) (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      p0037
  have p0039 :=
    @gMpbir (synWfn (synChncodepredfn) (synCvv))
      (synWfn (synCcom (synClnimageop)
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
        (synCvv))
      p0036 p0038
  have p0040 :=
    @gPm32i (synWfn (synCcom (synC2nd) (synC1st)) (synCvv))
      (synWfn (synChncodepredfn) (synCvv)) p0008 p0039
  have p0041 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC2nd) (synC1st)) (synChncodepredfn)
  have p0042 := Nominal.mp p0040 p0041
  have p0044 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0021
  have p0045 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) (synCvv))
      p0042 p0044
  have p0046 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0000 p0045
  have p0047 := (Nominal.classEqRefl (synChncodecarrierfn))
  have p0048 :=
    @gFneq1i (synCvv) (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      p0047
  have p0049 :=
    @gMpbir (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))) (synCvv))
      p0046 p0048
  have p0095 :=
    @gPm32i (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0049 p0049
  have p0096 := @gFntxp (synCvv) (synCvv) (synChncodecarrierfn) (synChncodecarrierfn)
  have p0097 := Nominal.mp p0095 p0096
  have p0099 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0021
  have p0100 :=
    @gMpbi
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) (synCvv)) p0097
      p0099
  have p0101 :=
    @gFncovv (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0004
      p0100
  have p0102 := (Nominal.classEqRefl (synChncodesquarefn))
  have p0103 :=
    @gFneq1i (synCvv) (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      p0102
  have p0104 :=
    @gMpbir (synWfn (synChncodesquarefn) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
        (synCvv))
      p0101 p0103
  have p0105 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synChncodesquarefn) (synCvv)) p0003 p0104
  have p0106 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st)) (synChncodesquarefn)
  have p0107 := Nominal.mp p0105 p0106
  have p0109 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0021
  have p0110 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) (synCvv))
      p0107 p0109
  have p0111 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0000 p0110
  have p0112 := (Nominal.classEqRefl (synChncoderelfn))
  have p0113 :=
    @gFneq1i (synCvv) (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      p0112
  have p0114 :=
    @gMpbir (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))) (synCvv))
      p0111 p0113
  have p0160 :=
    @gPm32i (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0114 p0049
  have p0161 := @gFntxp (synCvv) (synCvv) (synChncoderelfn) (synChncodecarrierfn)
  have p0162 := Nominal.mp p0160 p0161
  have p0164 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0021
  have p0165 :=
    @gMpbi
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn)) (synCvv)) p0162 p0164
  have p0166 := (Nominal.classEqRefl (synChncodecutfn))
  have p0167 :=
    @gFneq1i (synCvv) (synChncodecutfn)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0166
  have p0168 :=
    @gMpbir (synWfn (synChncodecutfn) (synCvv))
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn)) (synCvv)) p0165 p0167
  have p0170 :=
    @gPm32i (synWfn (synChncodecutfn) (synCvv)) (synWfn (synC1st) (synCvv)) p0168
      p0001
  have p0171 := @gFntxp (synCvv) (synCvv) (synChncodecutfn) (synC1st)
  have p0172 := Nominal.mp p0170 p0171
  have p0174 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncodecutfn) (synC1st)) p0021
  have p0175 :=
    @gMpbi
      (synWfn (synCtxp (synChncodecutfn) (synC1st)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncodecutfn) (synC1st)) (synCvv)) p0172 p0174
  have p0176 := (Nominal.classEqRefl (synChncodecutpairfn))
  have p0177 :=
    @gFneq1i (synCvv) (synChncodecutpairfn) (synCtxp (synChncodecutfn) (synC1st))
      p0176
  have p0178 :=
    @gMpbir (synWfn (synChncodecutpairfn) (synCvv))
      (synWfn (synCtxp (synChncodecutfn) (synC1st)) (synCvv)) p0175 p0177
  exact p0178

/-- Checked nominal proof certificate identified upstream as `g_hncodecutpairfnex`. -/
@[expose]
noncomputable def gHncodecutpairfnex :
    Nominal.NPrf (.classMem (synChncodecutpairfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodecutpairfn))
  have p0001 := (Nominal.classEqRefl (synChncodecutfn))
  have p0002 := (Nominal.classEqRefl (synChncoderelfn))
  have p0003 := @gLninteropex
  have p0004 := @gN1stex
  have p0006 := @gCoex (synC1st) (synC1st) p0004 p0004
  have p0007 := (Nominal.classEqRefl (synChncodesquarefn))
  have p0008 := @gCrossex
  have p0009 := (Nominal.classEqRefl (synChncodecarrierfn))
  have p0011 := @gN2ndex
  have p0013 := @gCoex (synC2nd) (synC1st) p0011 p0004
  have p0014 := (Nominal.classEqRefl (synChncodepredfn))
  have p0015 := @gLnimageopex
  have p0016 := @gSwapex
  have p0017 := @gImageex (synCswap) p0016
  have p0018 := (Nominal.classEqRefl (synChncodestrictfn))
  have p0019 := @gLndifopex
  have p0023 := @gVvex
  have p0024 := @gSnex (synCid)
  have p0025 := @gXpex (synCvv) (synCsn (synCid)) p0023 p0024
  have p0026 :=
    @gTxpex (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid)))
      p0006 p0025
  have p0027 :=
    @gCoex (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0019 p0026
  have p0028 :=
    @gEqeltri (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      (synCvv) p0018 p0027
  have p0029 := @gCoex (synCimage (synCswap)) (synChncodestrictfn) p0017 p0028
  have p0031 :=
    @gTxpex (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd) p0029
      p0011
  have p0032 :=
    @gCoex (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0015 p0031
  have p0033 :=
    @gEqeltri (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      (synCvv) p0014 p0032
  have p0034 := @gTxpex (synCcom (synC2nd) (synC1st)) (synChncodepredfn) p0013 p0033
  have p0035 :=
    @gCoex (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0003 p0034
  have p0036 :=
    @gEqeltri (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      (synCvv) p0009 p0035
  have p0065 := @gTxpex (synChncodecarrierfn) (synChncodecarrierfn) p0036 p0036
  have p0066 :=
    @gCoex (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0008
      p0065
  have p0067 :=
    @gEqeltri (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      (synCvv) p0007 p0066
  have p0068 :=
    @gTxpex (synCcom (synC1st) (synC1st)) (synChncodesquarefn) p0006 p0067
  have p0069 :=
    @gCoex (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0003 p0068
  have p0070 :=
    @gEqeltri (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      (synCvv) p0002 p0069
  have p0099 := @gTxpex (synChncoderelfn) (synChncodecarrierfn) p0070 p0036
  have p0100 :=
    @gEqeltri (synChncodecutfn) (synCtxp (synChncoderelfn) (synChncodecarrierfn))
      (synCvv) p0001 p0099
  have p0102 := @gTxpex (synChncodecutfn) (synC1st) p0100 p0004
  have p0103 :=
    @gEqeltri (synChncodecutpairfn) (synCtxp (synChncodecutfn) (synC1st)) (synCvv)
      p0000 p0102
  exact p0103


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecutfnval`. -/
@[expose]
noncomputable def gHncodecutfnval (x : Var) (D : Class) (R : Class)
    (hyp_hncodecutfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hncodecutfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChncodecutfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synChnwcutcode R D (.cv x))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodecutfn))
  have p0001 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncodecutfn)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0000
  have p0002 := @gLninteropfn
  have p0003 := @gLn1stfn
  have p0005 := @gFncovv (synC1st) (synC1st) p0003 p0003
  have p0006 := @gFncross
  have p0008 := @gLn2ndfn
  have p0010 := @gFncovv (synC2nd) (synC1st) p0008 p0003
  have p0011 := @gLnimageopfn
  have p0012 := @gImageswapfn
  have p0013 := @gFnlndifop
  have p0017 := @gIdex
  have p0018 := @gFnconstg (synCvv) (synCid) (synCvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCid))) (synCvv)) p0005 p0019
  have p0021 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st))
      (synCxp (synCvv) (synCsn (synCid)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @gInidm (synCvv)
  have p0024 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0023
  have p0025 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCvv))
      p0022 p0024
  have p0026 :=
    @gFncovv (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0013 p0025
  have p0027 := (Nominal.classEqRefl (synChncodestrictfn))
  have p0028 :=
    @gFneq1i (synCvv) (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      p0027
  have p0029 :=
    @gMpbir (synWfn (synChncodestrictfn) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid))))) (synCvv))
      p0026 p0028
  have p0030 := @gFncovv (synCimage (synCswap)) (synChncodestrictfn) p0012 p0029
  have p0032 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0030 p0008
  have p0033 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synCimage (synCswap)) (synChncodestrictfn))
      (synC2nd)
  have p0034 := Nominal.mp p0032 p0033
  have p0036 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0023
  have p0037 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCvv))
      p0034 p0036
  have p0038 :=
    @gFncovv (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0011 p0037
  have p0039 := (Nominal.classEqRefl (synChncodepredfn))
  have p0040 :=
    @gFneq1i (synCvv) (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      p0039
  have p0041 :=
    @gMpbir (synWfn (synChncodepredfn) (synCvv))
      (synWfn (synCcom (synClnimageop)
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
        (synCvv))
      p0038 p0040
  have p0042 :=
    @gPm32i (synWfn (synCcom (synC2nd) (synC1st)) (synCvv))
      (synWfn (synChncodepredfn) (synCvv)) p0010 p0041
  have p0043 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC2nd) (synC1st)) (synChncodepredfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0023
  have p0047 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) (synCvv))
      p0044 p0046
  have p0048 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0002 p0047
  have p0049 := (Nominal.classEqRefl (synChncodecarrierfn))
  have p0050 :=
    @gFneq1i (synCvv) (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      p0049
  have p0051 :=
    @gMpbir (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))) (synCvv))
      p0048 p0050
  have p0097 :=
    @gPm32i (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0051 p0051
  have p0098 := @gFntxp (synCvv) (synCvv) (synChncodecarrierfn) (synChncodecarrierfn)
  have p0099 := Nominal.mp p0097 p0098
  have p0101 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0023
  have p0102 :=
    @gMpbi
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) (synCvv)) p0099
      p0101
  have p0103 :=
    @gFncovv (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0006
      p0102
  have p0104 := (Nominal.classEqRefl (synChncodesquarefn))
  have p0105 :=
    @gFneq1i (synCvv) (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      p0104
  have p0106 :=
    @gMpbir (synWfn (synChncodesquarefn) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
        (synCvv))
      p0103 p0105
  have p0107 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synChncodesquarefn) (synCvv)) p0005 p0106
  have p0108 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st)) (synChncodesquarefn)
  have p0109 := Nominal.mp p0107 p0108
  have p0111 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0023
  have p0112 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) (synCvv))
      p0109 p0111
  have p0113 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0002 p0112
  have p0114 := (Nominal.classEqRefl (synChncoderelfn))
  have p0115 :=
    @gFneq1i (synCvv) (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      p0114
  have p0116 :=
    @gMpbir (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))) (synCvv))
      p0113 p0115
  have p0162 := @gOpex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0163 := @gSnex (.cv x)
  have p0164 := @gOpex (synCop R D) (synCsn (.cv x)) p0162 p0163
  have p0165 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x))) (synChncoderelfn)
      (synChncodecarrierfn) p0116 p0051 p0164
  have p0167 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      p0114
  have p0281 :=
    @gPm32i
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0112 p0164
  have p0282 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
  have p0283 := Nominal.mp p0281 p0282
  have p0391 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x))) (synCcom (synC1st) (synC1st))
      (synChncodesquarefn) p0005 p0106 p0164
  have p0396 :=
    @gPm32i (synWfn (synC1st) (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0003 p0164
  have p0397 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synC1st) (synC1st)
  have p0398 := Nominal.mp p0396 p0397
  have p0401 := @gOpfv1st (synCop R D) (synCsn (.cv x)) p0162 p0163
  have p0402 :=
    @gFveq2i (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))) (synCop R D)
      (synC1st) p0401
  have p0403 := @gOpfv1st R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0404 :=
    @gEqtri
      (synCfv (synC1st) (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synC1st) (synCop R D)) R p0402 p0403
  have p0405 :=
    @gEqtri
      (synCfv (synCcom (synC1st) (synC1st)) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synC1st) (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))))
      R p0398 p0404
  have p0407 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      p0104
  have p0507 :=
    @gPm32i (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0102 p0164
  have p0508 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synCcross)
      (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
  have p0509 := Nominal.mp p0507 p0508
  have p0603 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x))) (synChncodecarrierfn)
      (synChncodecarrierfn) p0051 p0051 p0164
  have p0605 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      p0049
  have p0649 :=
    @gPm32i
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0047 p0164
  have p0650 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
  have p0651 := Nominal.mp p0649 p0650
  have p0689 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x))) (synCcom (synC2nd) (synC1st))
      (synChncodepredfn) p0010 p0041 p0164
  have p0695 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synC2nd) (synC1st)
  have p0696 := Nominal.mp p0396 p0695
  have p0700 :=
    @gFveq2i (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))) (synCop R D)
      (synC2nd) p0401
  have p0701 := @gOpfv2nd R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0702 :=
    @gEqtri
      (synCfv (synC2nd) (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synC2nd) (synCop R D)) D p0700 p0701
  have p0703 :=
    @gEqtri
      (synCfv (synCcom (synC2nd) (synC1st)) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synC2nd) (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))))
      D p0696 p0702
  have p0705 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      p0039
  have p0735 :=
    @gPm32i
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0037 p0164
  have p0736 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
  have p0737 := Nominal.mp p0735 p0736
  have p0761 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x)))
      (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd) p0030 p0008
      p0164
  have p0782 :=
    @gPm32i (synWfn (synChncodestrictfn) (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0029 p0164
  have p0783 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synCimage (synCswap))
      (synChncodestrictfn)
  have p0784 := Nominal.mp p0782 p0783
  have p0786 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      p0027
  have p0802 :=
    @gPm32i
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCvv))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCvv)) p0025 p0164
  have p0803 :=
    @gFvco2 (synCvv) (synCop (synCop R D) (synCsn (.cv x))) (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
  have p0804 := Nominal.mp p0802 p0803
  have p0814 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x))) (synCcom (synC1st) (synC1st))
      (synCxp (synCvv) (synCsn (synCid))) p0005 p0019 p0164
  have p0833 :=
    @gFvconst2 (synCvv) (synCid) (synCop (synCop R D) (synCsn (.cv x))) p0017
  have p0834 := Nominal.mp p0164 p0833
  have p0835 :=
    @gOpeq12i
      (synCfv (synCcom (synC1st) (synC1st)) (synCop (synCop R D) (synCsn (.cv x))))
      R
      (synCfv (synCxp (synCvv) (synCsn (synCid)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCid) p0405 p0834
  have p0836 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synCcom (synC1st) (synC1st))
          (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synCxp (synCvv) (synCsn (synCid)))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop R (synCid)) p0814 p0835
  have p0837 :=
    @gFveq2i
      (synCfv (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCop (synCop R D) (synCsn (.cv x))))
      (synCop R (synCid)) (synClndifop) p0836
  have p0838 := (Nominal.classEqRefl (synCo R (synClndifop) (synCid)))
  have p0839 :=
    @gEqcomi (synCo R (synClndifop) (synCid))
      (synCfv (synClndifop) (synCop R (synCid))) p0838
  have p0841 :=
    @gPm32i (.classMem R (synCvv)) (.classMem (synCid) (synCvv)) hyp_hncodecutfnval_1
      p0017
  have p0842 := @gLndifopvalg R (synCid) (synCvv) (synCvv)
  have p0843 := Nominal.mp p0841 p0842
  have p0844 :=
    @gEqtri (synCfv (synClndifop) (synCop R (synCid)))
      (synCo R (synClndifop) (synCid)) (synCdif R (synCid)) p0839 p0843
  have p0845 :=
    @gEqtri
      (synCfv (synClndifop) (synCfv (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid)))) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synClndifop) (synCop R (synCid))) (synCdif R (synCid)) p0837 p0844
  have p0846 :=
    @gEqtri
      (synCfv (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid))))) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synClndifop) (synCfv (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid)))) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCdif R (synCid)) p0804 p0845
  have p0847 :=
    @gEqtri (synCfv (synChncodestrictfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid))))) (synCop (synCop R D) (synCsn (.cv x))))
      (synCdif R (synCid)) p0786 p0846
  have p0848 :=
    @gFveq2i (synCfv (synChncodestrictfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCdif R (synCid)) (synCimage (synCswap)) p0847
  have p0850 := @gDifex R (synCid) hyp_hncodecutfnval_1 p0017
  have p0851 := @gWppimageswapfv (synCdif R (synCid)) p0850
  have p0852 :=
    @gEqtri
      (synCfv (synCimage (synCswap))
        (synCfv (synChncodestrictfn) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synCimage (synCswap)) (synCdif R (synCid)))
      (synCcnv (synCdif R (synCid))) p0848 p0851
  have p0853 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synChncodestrictfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCimage (synCswap))
        (synCfv (synChncodestrictfn) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCcnv (synCdif R (synCid))) p0784 p0852
  have p0856 := @gOpfv2nd (synCop R D) (synCsn (.cv x)) p0162 p0163
  have p0857 :=
    @gOpeq12i
      (synCfv (synCcom (synCimage (synCswap)) (synChncodestrictfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCcnv (synCdif R (synCid)))
      (synCfv (synC2nd) (synCop (synCop R D) (synCsn (.cv x)))) (synCsn (.cv x))
      p0853 p0856
  have p0858 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synCcom (synCimage (synCswap)) (synChncodestrictfn))
          (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synC2nd) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0761 p0857
  have p0859 :=
    @gFveq2i
      (synCfv (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) (synClnimageop) p0858
  have p0862 := @gCnvex (synCdif R (synCid)) p0850
  have p0864 :=
    @gLnimageopval (synCsn (.cv x)) (synCcnv (synCdif R (synCid))) p0862 p0163
  have p0865 :=
    @gEqtri
      (synCfv (synClnimageop) (synCfv
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synClnimageop) (synCop (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0859 p0864
  have p0866 :=
    @gEqtri
      (synCfv (synCcom (synClnimageop)
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synClnimageop) (synCfv
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0737 p0865
  have p0867 :=
    @gEqtri (synCfv (synChncodepredfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCcom (synClnimageop)
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0705 p0866
  have p0868 :=
    @gOpeq12i
      (synCfv (synCcom (synC2nd) (synC1st)) (synCop (synCop R D) (synCsn (.cv x))))
      D (synCfv (synChncodepredfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0703 p0867
  have p0869 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synCcom (synC2nd) (synC1st))
          (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synChncodepredfn) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0689
      p0868
  have p0870 :=
    @gFveq2i
      (synCfv (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synClninterop) p0869
  have p0875 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0862 p0163
  have p0876 :=
    @gLninteropval D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      hyp_hncodecutfnval_2 p0875
  have p0877 :=
    @gEqtri
      (synCfv (synClninterop)
        (synCfv (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synClninterop)
        (synCop D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0870
      p0876
  have p0878 :=
    @gEqtri
      (synCfv (synCcom (synClninterop)
          (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synClninterop)
        (synCfv (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0651
      p0877
  have p0879 :=
    @gEqtri (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCcom (synClninterop)
          (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0605
      p0878
  have p1156 :=
    @gOpeq12i (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0879
      p0879
  have p1157 :=
    @gEqtri
      (synCfv (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0603 p1156
  have p1158 :=
    @gFveq2i
      (synCfv (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCcross) p1157
  have p1159 :=
    (Nominal.classEqRefl
      (synCo (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCcross)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p1160 :=
    @gEqcomi
      (synCo (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCcross) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCfv (synCcross) (synCop
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p1159
  have p1166 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      hyp_hncodecutfnval_2 p0875
  have p1173 :=
    @gPm32i
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      (.classMem (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCvv))
      p1166 p1166
  have p1174 :=
    @gOvcross (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCvv)
      (synCvv)
  have p1175 := Nominal.mp p1173 p1174
  have p1176 :=
    @gEqtri
      (synCfv (synCcross) (synCop
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCo (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCcross) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p1160 p1175
  have p1177 :=
    @gEqtri
      (synCfv (synCcross) (synCfv (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synCcross) (synCop
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p1158 p1176
  have p1178 :=
    @gEqtri
      (synCfv (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCcross) (synCfv (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0509 p1177
  have p1179 :=
    @gEqtri (synCfv (synChncodesquarefn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0407 p1178
  have p1180 :=
    @gOpeq12i
      (synCfv (synCcom (synC1st) (synC1st)) (synCop (synCop R D) (synCsn (.cv x))))
      R (synCfv (synChncodesquarefn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0405 p1179
  have p1181 :=
    @gEqtri
      (synCfv (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synCcom (synC1st) (synC1st))
          (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synChncodesquarefn) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0391 p1180
  have p1182 :=
    @gFveq2i
      (synCfv (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synClninterop) p1181
  have p1195 :=
    @gXpex (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p1166
      p1166
  have p1196 :=
    @gLninteropval R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      hyp_hncodecutfnval_1 p1195
  have p1197 :=
    @gEqtri
      (synCfv (synClninterop)
        (synCfv (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCfv (synClninterop) (synCop R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p1182 p1196
  have p1198 :=
    @gEqtri
      (synCfv (synCcom (synClninterop)
          (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synClninterop)
        (synCfv (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
          (synCop (synCop R D) (synCsn (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0283 p1197
  have p1199 :=
    @gEqtri (synCfv (synChncoderelfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCcom (synClninterop)
          (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0167 p1198
  have p1476 :=
    @gOpeq12i (synCfv (synChncoderelfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p1199
      p0879
  have p1477 :=
    @gEqtri
      (synCfv (synCtxp (synChncoderelfn) (synChncodecarrierfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synChncoderelfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synChncodecarrierfn) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0165 p1476
  have p1478 :=
    @gEqtri (synCfv (synChncodecutfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCtxp (synChncoderelfn) (synChncodecarrierfn))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0001 p1477
  have p1479 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p1480 :=
    @gEqcomi (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p1479
  have p1481 :=
    @gEqtri (synCfv (synChncodecutfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synChnwcutcode R D (.cv x)) p1478 p1480
  exact p1481


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecutpairfnval`. -/
@[expose]
noncomputable def gHncodecutpairfnval (x : Var) (D : Class) (R : Class)
    (hyp_hncodecutpairfnval_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hncodecutpairfnval_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synChncodecutpairfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCop (synChnwcutcode R D (.cv x)) (synCop R D))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodecutpairfn))
  have p0001 :=
    @gFveq1i (synCop (synCop R D) (synCsn (.cv x))) (synChncodecutpairfn)
      (synCtxp (synChncodecutfn) (synC1st)) p0000
  have p0002 := @gLninteropfn
  have p0003 := @gLn1stfn
  have p0005 := @gFncovv (synC1st) (synC1st) p0003 p0003
  have p0006 := @gFncross
  have p0008 := @gLn2ndfn
  have p0010 := @gFncovv (synC2nd) (synC1st) p0008 p0003
  have p0011 := @gLnimageopfn
  have p0012 := @gImageswapfn
  have p0013 := @gFnlndifop
  have p0017 := @gIdex
  have p0018 := @gFnconstg (synCvv) (synCid) (synCvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synCxp (synCvv) (synCsn (synCid))) (synCvv)) p0005 p0019
  have p0021 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st))
      (synCxp (synCvv) (synCsn (synCid)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @gInidm (synCvv)
  have p0024 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0023
  have p0025 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))) (synCvv))
      p0022 p0024
  have p0026 :=
    @gFncovv (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0013 p0025
  have p0027 := (Nominal.classEqRefl (synChncodestrictfn))
  have p0028 :=
    @gFneq1i (synCvv) (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      p0027
  have p0029 :=
    @gMpbir (synWfn (synChncodestrictfn) (synCvv))
      (synWfn (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
            (synCxp (synCvv) (synCsn (synCid))))) (synCvv))
      p0026 p0028
  have p0030 := @gFncovv (synCimage (synCswap)) (synChncodestrictfn) p0012 p0029
  have p0032 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synCvv))
      (synWfn (synC2nd) (synCvv)) p0030 p0008
  have p0033 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synCimage (synCswap)) (synChncodestrictfn))
      (synC2nd)
  have p0034 := Nominal.mp p0032 p0033
  have p0036 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0023
  have p0037 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
        (synCvv))
      p0034 p0036
  have p0038 :=
    @gFncovv (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0011 p0037
  have p0039 := (Nominal.classEqRefl (synChncodepredfn))
  have p0040 :=
    @gFneq1i (synCvv) (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      p0039
  have p0041 :=
    @gMpbir (synWfn (synChncodepredfn) (synCvv))
      (synWfn (synCcom (synClnimageop)
          (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
        (synCvv))
      p0038 p0040
  have p0042 :=
    @gPm32i (synWfn (synCcom (synC2nd) (synC1st)) (synCvv))
      (synWfn (synChncodepredfn) (synCvv)) p0010 p0041
  have p0043 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC2nd) (synC1st)) (synChncodepredfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0023
  have p0047 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) (synCvv))
      p0044 p0046
  have p0048 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0002 p0047
  have p0049 := (Nominal.classEqRefl (synChncodecarrierfn))
  have p0050 :=
    @gFneq1i (synCvv) (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      p0049
  have p0051 :=
    @gMpbir (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn))) (synCvv))
      p0048 p0050
  have p0097 :=
    @gPm32i (synWfn (synChncodecarrierfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0051 p0051
  have p0098 := @gFntxp (synCvv) (synCvv) (synChncodecarrierfn) (synChncodecarrierfn)
  have p0099 := Nominal.mp p0097 p0098
  have p0101 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0023
  have p0102 :=
    @gMpbi
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) (synCvv)) p0099
      p0101
  have p0103 :=
    @gFncovv (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0006
      p0102
  have p0104 := (Nominal.classEqRefl (synChncodesquarefn))
  have p0105 :=
    @gFneq1i (synCvv) (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      p0104
  have p0106 :=
    @gMpbir (synWfn (synChncodesquarefn) (synCvv))
      (synWfn (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
        (synCvv))
      p0103 p0105
  have p0107 :=
    @gPm32i (synWfn (synCcom (synC1st) (synC1st)) (synCvv))
      (synWfn (synChncodesquarefn) (synCvv)) p0005 p0106
  have p0108 :=
    @gFntxp (synCvv) (synCvv) (synCcom (synC1st) (synC1st)) (synChncodesquarefn)
  have p0109 := Nominal.mp p0107 p0108
  have p0111 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0023
  have p0112 :=
    @gMpbi
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) (synCvv))
      p0109 p0111
  have p0113 :=
    @gFncovv (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0002 p0112
  have p0114 := (Nominal.classEqRefl (synChncoderelfn))
  have p0115 :=
    @gFneq1i (synCvv) (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      p0114
  have p0116 :=
    @gMpbir (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synCcom (synClninterop)
          (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn))) (synCvv))
      p0113 p0115
  have p0162 :=
    @gPm32i (synWfn (synChncoderelfn) (synCvv))
      (synWfn (synChncodecarrierfn) (synCvv)) p0116 p0051
  have p0163 := @gFntxp (synCvv) (synCvv) (synChncoderelfn) (synChncodecarrierfn)
  have p0164 := Nominal.mp p0162 p0163
  have p0166 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0023
  have p0167 :=
    @gMpbi
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn)) (synCvv)) p0164 p0166
  have p0168 := (Nominal.classEqRefl (synChncodecutfn))
  have p0169 :=
    @gFneq1i (synCvv) (synChncodecutfn)
      (synCtxp (synChncoderelfn) (synChncodecarrierfn)) p0168
  have p0170 :=
    @gMpbir (synWfn (synChncodecutfn) (synCvv))
      (synWfn (synCtxp (synChncoderelfn) (synChncodecarrierfn)) (synCvv)) p0167 p0169
  have p0172 := @gOpex R D hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0173 := @gSnex (.cv x)
  have p0174 := @gOpex (synCop R D) (synCsn (.cv x)) p0172 p0173
  have p0175 :=
    @gFvtxpvv (synCop (synCop R D) (synCsn (.cv x))) (synChncodecutfn) (synC1st)
      p0170 p0003 p0174
  have p0176 := @gHncodecutfnval x D R hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0179 := @gOpfv1st (synCop R D) (synCsn (.cv x)) p0172 p0173
  have p0180 :=
    @gOpeq12i (synCfv (synChncodecutfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synChnwcutcode R D (.cv x))
      (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))) (synCop R D) p0176
      p0179
  have p0181 :=
    @gEqtri
      (synCfv (synCtxp (synChncodecutfn) (synC1st))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synCfv (synChncodecutfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCfv (synC1st) (synCop (synCop R D) (synCsn (.cv x)))))
      (synCop (synChnwcutcode R D (.cv x)) (synCop R D)) p0175 p0180
  have p0182 :=
    @gEqtri (synCfv (synChncodecutpairfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCfv (synCtxp (synChncodecutfn) (synC1st))
        (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synChnwcutcode R D (.cv x)) (synCop R D)) p0001 p0181
  exact p0182

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsetexg`. -/
@[expose]
noncomputable def gHncodecmpsetexg (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (.classMem (synChncodecmpset A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodecmpset A))
  have p0001 := @gHwnisoexg A
  have p0002 := (Nominal.classEqRefl (synChncodecutrel A))
  have p0003 := @gHncodecutpairfnex
  have p0004 :=
    @gA1i (.classMem (synChncodecutpairfn) (synCvv)) (.classMem A (synCvv)) p0003
  have p0005 := (Nominal.classEqRefl (synChncodecutinputs A))
  have p0006 := @gLnpwquoinputfnex
  have p0007 :=
    @gA1i (.classMem (synClnpwquoinputfn) (synCvv)) (.classMem A (synCvv)) p0006
  have p0008 := @gHwcnexg A
  have p0009 := @gPw1exg (synChwcn A) (synCvv)
  have p0010 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))
      (.classMem (synCpw1 (synChwcn A)) (synCvv)) p0008 p0009
  have p0011 :=
    @gJca (.classMem A (synCvv)) (.classMem (synClnpwquoinputfn) (synCvv))
      (.classMem (synCpw1 (synChwcn A)) (synCvv)) p0007 p0010
  have p0012 :=
    @gImaexg (synClnpwquoinputfn) (synCpw1 (synChwcn A)) (synCvv) (synCvv)
  have p0013 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synClnpwquoinputfn) (synCvv))
        (.classMem (synCpw1 (synChwcn A)) (synCvv)))
      (.classMem (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))) (synCvv))
      p0011 p0012
  have p0014 :=
    @gUniexg (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))) (synCvv)
  have p0015 :=
    @gSyl (.classMem A (synCvv))
      (.classMem (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))) (synCvv))
      (.classMem (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))) (synCvv))
      p0013 p0014
  have p0016 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChncodecutinputs A)
      (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))) (synCvv) p0005
      p0015
  have p0017 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChncodecutpairfn) (synCvv))
      (.classMem (synChncodecutinputs A) (synCvv)) p0004 p0016
  have p0018 :=
    @gImaexg (synChncodecutpairfn) (synChncodecutinputs A) (synCvv) (synCvv)
  have p0019 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChncodecutpairfn) (synCvv))
        (.classMem (synChncodecutinputs A) (synCvv)))
      (.classMem (synCima (synChncodecutpairfn) (synChncodecutinputs A)) (synCvv))
      p0017 p0018
  have p0020 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChncodecutrel A)
      (synCima (synChncodecutpairfn) (synChncodecutinputs A)) (synCvv) p0002 p0019
  have p0022 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChncodecutrel A) (synCvv))
      (.classMem (synChwniso A) (synCvv)) p0020 p0001
  have p0023 := @gCoexg (synChncodecutrel A) (synChwniso A) (synCvv) (synCvv)
  have p0024 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChncodecutrel A) (synCvv)) (.classMem (synChwniso A) (synCvv)))
      (.classMem (synCcom (synChncodecutrel A) (synChwniso A)) (synCvv)) p0022 p0023
  have p0025 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwniso A) (synCvv))
      (.classMem (synCcom (synChncodecutrel A) (synChwniso A)) (synCvv)) p0001 p0024
  have p0026 :=
    @gUnexg (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A)) (synCvv)
      (synCvv)
  have p0027 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwniso A) (synCvv))
        (.classMem (synCcom (synChncodecutrel A) (synChwniso A)) (synCvv)))
      (.classMem (synCun (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A)))
        (synCvv))
      p0025 p0026
  have p0028 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChncodecmpset A)
      (synCun (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A))) (synCvv)
      p0000 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_brhncodecmpset`. -/
@[expose]
noncomputable def gBrhncodecmpset (x : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex x
            (synWa (synWbr (.cv u) (synChwniso A) (.cv x))
              (synWbr (.cv x) (synChncodecutrel A) (.cv v)))))) :=
  by
  have dv_cache_0001 : x ∉ ((Class.cv u)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_u_x), not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_v_x), not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synChncodecutrel A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
          dv_A_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_x,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChncodecmpset A))
  have p0001 :=
    @gBreqi (.cv u) (.cv v) (synChncodecmpset A)
      (synCun (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A))) p0000
  have p0002 :=
    @gBrun (.cv u) (.cv v) (synChwniso A)
      (synCcom (synChncodecutrel A) (synChwniso A))
  have p0003 :=
    @gBrco x (.cv u) (.cv v) (synChncodecutrel A) (synChwniso A) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gOrbi2i (synWbr (.cv u) (synCcom (synChncodecutrel A) (synChwniso A)) (.cv v))
      (synWex x (synWa (synWbr (.cv u) (synChwniso A) (.cv x))
          (synWbr (.cv x) (synChncodecutrel A) (.cv v))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0003
  have p0005 :=
    @gBitri
      (synWbr (.cv u)
        (synCun (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A))) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv u) (synCcom (synChncodecutrel A) (synChwniso A)) (.cv v)))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex x
          (synWa (synWbr (.cv u) (synChwniso A) (.cv x))
            (synWbr (.cv x) (synChncodecutrel A) (.cv v)))))
      p0002 p0004
  have p0006 :=
    @gBitri (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv u)
        (synCun (synChwniso A) (synCcom (synChncodecutrel A) (synChwniso A))) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex x
          (synWa (synWbr (.cv u) (synChwniso A) (.cv x))
            (synWbr (.cv x) (synChncodecutrel A) (.cv v)))))
      p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hncodecutinputmemi`. -/
@[expose]
noncomputable def gHncodecutinputmemi (x : Var) (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_hncodecutinputmemi_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hncodecutinputmemi_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
        (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synChncodecutinputs A))) :=
  by
  have p0000 := @gOpex R D hyp_hncodecutinputmemi_1 hyp_hncodecutinputmemi_2
  have p0001 := @gSnid (synCop R D) p0000
  have p0002 :=
    @gA1i (.classMem (synCop R D) (synCsn (synCop R D)))
      (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)) p0001
  have p0003 := @gSimpr (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)
  have p0004 := @gSnelpw1 (.cv x) D
  have p0005 :=
    @gSylibr (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) (.classMem (synCsn (.cv x)) (synCpw1 D)) p0003 p0004
  have p0006 :=
    @gJca (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (synCop R D) (synCsn (synCop R D)))
      (.classMem (synCsn (.cv x)) (synCpw1 D)) p0002 p0005
  have p0007 :=
    @gOpelxp (synCop R D) (synCsn (.cv x)) (synCsn (synCop R D)) (synCpw1 D)
  have p0008 :=
    @gSylibr (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (synWa (.classMem (synCop R D) (synCsn (synCop R D)))
        (.classMem (synCsn (.cv x)) (synCpw1 D)))
      (.classMem (synCop (synCop R D) (synCsn (.cv x)))
        (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      p0006 p0007
  have p0009 := @gLnpwquoinputfnval D R hyp_hncodecutinputmemi_1 hyp_hncodecutinputmemi_2
  have p0010 :=
    @gA1i
      (.classEq (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
        (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)) p0009
  have p0011 := @gSimpl (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)
  have p0012 := @gSnelpw1 (synCop R D) (synChwcn A)
  have p0013 :=
    @gSylibr (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (synCop R D) (synChwcn A))
      (.classMem (synCsn (synCop R D)) (synCpw1 (synChwcn A))) p0011 p0012
  have p0014 := @gLnpwquoinputfnfn
  have p0015 := @gFnfun (synCvv) (synClnpwquoinputfn)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gSnex (synCop R D)
  have p0019 := @gFndm (synCvv) (synClnpwquoinputfn)
  have p0020 := Nominal.mp p0014 p0019
  have p0021 :=
    @gEleqtrri (synCsn (synCop R D)) (synCvv) (synCdm (synClnpwquoinputfn)) p0017
      p0020
  have p0022 :=
    @gPm32i (synWfun (synClnpwquoinputfn))
      (.classMem (synCsn (synCop R D)) (synCdm (synClnpwquoinputfn))) p0016 p0021
  have p0023 :=
    @gFunfvima (synCpw1 (synChwcn A)) (synCsn (synCop R D)) (synClnpwquoinputfn)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gSyl (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (synCsn (synCop R D)) (synCpw1 (synChwcn A)))
      (.classMem (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
        (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
      p0013 p0024
  have p0026 :=
    @gEqeltrrd (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (synCfv (synClnpwquoinputfn) (synCsn (synCop R D)))
      (synCxp (synCsn (synCop R D)) (synCpw1 D))
      (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))) p0010 p0025
  have p0027 :=
    @gJca (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (synCop (synCop R D) (synCsn (.cv x)))
        (synCxp (synCsn (synCop R D)) (synCpw1 D)))
      (.classMem (synCxp (synCsn (synCop R D)) (synCpw1 D))
        (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
      p0008 p0026
  have p0028 :=
    @gElunii (synCop (synCop R D) (synCsn (.cv x)))
      (synCxp (synCsn (synCop R D)) (synCpw1 D))
      (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))
  have p0029 :=
    @gSyl (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (synWa (.classMem (synCop (synCop R D) (synCsn (.cv x)))
          (synCxp (synCsn (synCop R D)) (synCpw1 D)))
        (.classMem (synCxp (synCsn (synCop R D)) (synCpw1 D))
          (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (.classMem (synCop (synCop R D) (synCsn (.cv x)))
        (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      p0027 p0028
  have p0030 := (Nominal.classEqRefl (synChncodecutinputs A))
  have p0031 :=
    @gA1i
      (.classEq (synChncodecutinputs A)
        (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)) p0030
  have p0032 :=
    @gEleqtrrd (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (synCop (synCop R D) (synCsn (.cv x)))
      (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
      (synChncodecutinputs A) p0029 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_hncodecutreledgei`. -/
@[expose]
noncomputable def gHncodecutreledgei (x : Var) (A : Class) (D : Class) (R : Class)
    (dv_A_R : Disjoint A.fv R.fv)
    (hyp_hncodecutreledgei_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_hncodecutreledgei_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
        (synWbr (synChnwcutcode R D (.cv x)) (synChncodecutrel A) (synCop R D))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @gHncodecutpairfnval x D R hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0001 :=
    @gA1i
      (.classEq (synCfv (synChncodecutpairfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCop (synChnwcutcode R D (.cv x)) (synCop R D)))
      (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)) p0000
  have p0002 :=
    @gHncodecutinputmemi x A D R dv_cache_0001 hyp_hncodecutreledgei_1
      hyp_hncodecutreledgei_2
  have p0003 := @gHncodecutpairfnfn
  have p0004 := @gFnfun (synCvv) (synChncodecutpairfn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gOpex R D hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0007 := @gSnex (.cv x)
  have p0008 := @gOpex (synCop R D) (synCsn (.cv x)) p0006 p0007
  have p0010 := @gFndm (synCvv) (synChncodecutpairfn)
  have p0011 := Nominal.mp p0003 p0010
  have p0012 :=
    @gEleqtrri (synCop (synCop R D) (synCsn (.cv x))) (synCvv)
      (synCdm (synChncodecutpairfn)) p0008 p0011
  have p0013 :=
    @gPm32i (synWfun (synChncodecutpairfn))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synCdm (synChncodecutpairfn)))
      p0005 p0012
  have p0014 :=
    @gFunfvima (synChncodecutinputs A) (synCop (synCop R D) (synCsn (.cv x)))
      (synChncodecutpairfn)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @gSyl (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (synCop (synCop R D) (synCsn (.cv x))) (synChncodecutinputs A))
      (.classMem (synCfv (synChncodecutpairfn) (synCop (synCop R D) (synCsn (.cv x))))
        (synCima (synChncodecutpairfn) (synChncodecutinputs A)))
      p0002 p0015
  have p0017 :=
    @gEqeltrrd (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (synCfv (synChncodecutpairfn) (synCop (synCop R D) (synCsn (.cv x))))
      (synCop (synChnwcutcode R D (.cv x)) (synCop R D))
      (synCima (synChncodecutpairfn) (synChncodecutinputs A)) p0001 p0016
  have p0018 := (Nominal.classEqRefl (synChncodecutrel A))
  have p0019 :=
    @gA1i
      (.classEq (synChncodecutrel A)
        (synCima (synChncodecutpairfn) (synChncodecutinputs A)))
      (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @gEleqtrrd (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (synCop (synChnwcutcode R D (.cv x)) (synCop R D))
      (synCima (synChncodecutpairfn) (synChncodecutinputs A)) (synChncodecutrel A)
      p0017 p0019
  have p0021 :=
    (Nominal.biimpRefl
      (synWbr (synChnwcutcode R D (.cv x)) (synChncodecutrel A) (synCop R D)))
  have p0022 :=
    @gSylibr (synWa (.classMem (synCop R D) (synChwcn A)) (.classMem (.cv x) D))
      (.classMem (synCop (synChnwcutcode R D (.cv x)) (synCop R D)) (synChncodecutrel A))
      (synWbr (synChnwcutcode R D (.cv x)) (synChncodecutrel A) (synCop R D)) p0020
      p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_lnpwquoinputfnvalhwcn`. -/
@[expose]
noncomputable def gLnpwquoinputfnvalhwcn (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classEq (synCfv (synClnpwquoinputfn) (synCsn (.cv u)))
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))) :=
  by
  have p0000 := @gHwcnpair u A
  have p0001 :=
    @gSneqd (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) p0000
  have p0002 :=
    @gFveq2d (.classMem (.cv u) (synChwcn A)) (synCsn (.cv u))
      (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synClnpwquoinputfn) p0001
  have p0003 := @gFvex (.cv u) (synC1st)
  have p0004 := @gFvex (.cv u) (synC2nd)
  have p0005 :=
    @gLnpwquoinputfnval (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) p0003
      p0004
  have p0006 :=
    @gA1i
      (.classEq (synCfv (synClnpwquoinputfn)
          (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCxp (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
          (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) p0005
  have p0009 :=
    @gXpeq1d (.classMem (.cv u) (synChwcn A)) (synCsn (.cv u))
      (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCpw1 (synCfv (synC2nd) (.cv u))) p0001
  have p0010 :=
    @gEqcomd (.classMem (.cv u) (synChwcn A))
      (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCxp (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synCfv (synC2nd) (.cv u))))
      p0009
  have p0011 :=
    @gN3eqtrd (.classMem (.cv u) (synChwcn A))
      (synCfv (synClnpwquoinputfn) (synCsn (.cv u)))
      (synCfv (synClnpwquoinputfn)
        (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (synCxp (synCsn (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))) p0002 p0006
      p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hncodeinputproductdecode`. -/
@[expose]
noncomputable def gHncodeinputproductdecode (x : Var) (u : Var) (D : Class) (p : Var)
    (dv_D_x : x ∉ D.fv) (dv_p_x : p ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv p) (synCxp (synCsn (.cv u)) (synCpw1 D)))
        (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ D.fv ∪ ({ p } : Finset Var)
  let s : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_s_ne_u : s ≠ u := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_p : s ≠ p := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_p : w ≠ p := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_s_ne_w : s ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_s : w ≠ s := Ne.symm fresh_s_ne_w
  have fresh_s_ne_y : s ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_s : y ≠ s := Ne.symm fresh_s_ne_y
  have dv_cache_0001 : w ∉ ((Class.cv p)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_p, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_p, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((synCsn (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_u,
          not_false_eq_true])
  have dv_cache_0004 : s ∉ ((synCsn (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_s_ne_u,
          not_false_eq_true])
  have dv_cache_0005 : w ∉ ((synCpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_w_not_D,
          not_false_eq_true])
  have dv_cache_0006 : s ∉ ((synCpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_s_not_D,
          not_false_eq_true])
  have dv_cache_0007 : w ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show w ≠ s from (by exact fresh_w_ne_s))
  have dv_cache_0008 : s ∉ ((Wff.classEq (.cv w) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_w, fresh_s_ne_u, or_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_u, not_false_eq_true])
  have dv_cache_0010 :
    w ∉ ((synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv u) (.cv s))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_D, fresh_w_ne_p,
          fresh_w_ne_u, fresh_w_ne_s, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_s, not_false_eq_true])
  have dv_cache_0012 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0014 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0015 :
    x ∉ ((Wff.classEq (.cv p) (synCop (.cv u) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_p_x), (Ne.symm dv_u_x), fresh_x_ne_y,
          or_false, not_false_eq_true])
  have dv_cache_0016 :
    y ∉
      ((Wff.imp (.classEq (.cv p) (synCop (.cv u) (.cv s)))
          (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u,
          fresh_y_ne_s, fresh_y_not_D, fresh_y_ne_x, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 :
    s ∉ ((synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_s_not_D, fresh_s_ne_p,
          fresh_s_ne_u, fresh_s_ne_x, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gElxp2 w s (.cv p) (synCsn (.cv u)) (synCpw1 D) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @gVex u
  have p0002 := @gId (.classEq (.cv w) (.cv u))
  have p0003 := @gOpeq1d (.classEq (.cv w) (.cv u)) (.cv w) (.cv u) (.cv s) p0002
  have p0004 :=
    @gEqeq2d (.classEq (.cv w) (.cv u)) (synCop (.cv w) (.cv s))
      (synCop (.cv u) (.cv s)) (.cv p) p0003
  have p0005 :=
    @gRexbidv (.classEq (.cv w) (.cv u)) (.classEq (.cv p) (synCop (.cv w) (.cv s)))
      (.classEq (.cv p) (synCop (.cv u) (.cv s))) s (synCpw1 D) dv_cache_0008 p0004
  have p0006 :=
    @gRexsn (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv w) (.cv s))))
      (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv u) (.cv s)))) w (.cv u)
      dv_cache_0009 dv_cache_0010 p0001 p0005
  have p0007 :=
    @gBiimpi
      (synWrex w (synCsn (.cv u))
        (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv w) (.cv s)))))
      (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv u) (.cv s)))) p0006
  have p0008 :=
    @gSylbi (.classMem (.cv p) (synCxp (synCsn (.cv u)) (synCpw1 D)))
      (synWrex w (synCsn (.cv u))
        (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv w) (.cv s)))))
      (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv u) (.cv s)))) p0000 p0007
  have p0009 := @gElpw1 y (.cv s) D dv_cache_0011 dv_cache_0012
  have p0010 :=
    @gN3simpa (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
      (.classEq (.cv p) (synCop (.cv u) (.cv s)))
  have p0011 := @gSimpl (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
  have p0012 :=
    @gSyl
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (synWa (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y))))
      (.classMem (.cv y) D) p0010 p0011
  have p0013 :=
    @gN3simpc (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
      (.classEq (.cv p) (synCop (.cv u) (.cv s)))
  have p0014 :=
    @gSimpr (.classEq (.cv s) (synCsn (.cv y)))
      (.classEq (.cv p) (synCop (.cv u) (.cv s)))
  have p0015 :=
    @gSyl
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (synWa (.classEq (.cv s) (synCsn (.cv y))) (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (.classEq (.cv p) (synCop (.cv u) (.cv s))) p0013 p0014
  have p0017 :=
    @gSimpl (.classEq (.cv s) (synCsn (.cv y)))
      (.classEq (.cv p) (synCop (.cv u) (.cv s)))
  have p0018 :=
    @gSyl
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (synWa (.classEq (.cv s) (synCsn (.cv y))) (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (.classEq (.cv s) (synCsn (.cv y))) p0013 p0017
  have p0019 :=
    @gOpeq2d
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (.cv s) (synCsn (.cv y)) (.cv u) p0018
  have p0020 :=
    @gEqtrd
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (.cv p) (synCop (.cv u) (.cv s)) (synCop (.cv u) (synCsn (.cv y))) p0015 p0019
  have p0021 :=
    @gJca
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (.classMem (.cv y) D) (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv y)))) p0012
      p0020
  have p0022 := @gId (.classEq (.cv x) (.cv y))
  have p0023 := @gSneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0022
  have p0024 :=
    @gOpeq2d (.classEq (.cv x) (.cv y)) (synCsn (.cv x)) (synCsn (.cv y)) (.cv u) p0023
  have p0025 :=
    @gEqeq2d (.classEq (.cv x) (.cv y)) (synCop (.cv u) (synCsn (.cv x)))
      (synCop (.cv u) (synCsn (.cv y))) (.cv p) p0024
  have p0026 :=
    @gRspcev (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))
      (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv y)))) x (.cv y) D dv_cache_0013
      dv_cache_0014 dv_cache_0015 p0025
  have p0027 :=
    @gSyl
      (synW3a (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
        (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (synWa (.classMem (.cv y) D) (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv y)))))
      (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))) p0021 p0026
  have p0028 :=
    @gN3exp (.classMem (.cv y) D) (.classEq (.cv s) (synCsn (.cv y)))
      (.classEq (.cv p) (synCop (.cv u) (.cv s)))
      (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))) p0027
  have p0029 :=
    @gRexlimiv (.classEq (.cv s) (synCsn (.cv y)))
      (.imp (.classEq (.cv p) (synCop (.cv u) (.cv s)))
        (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))
      y D dv_cache_0016 p0028
  have p0030 :=
    @gSylbi (.classMem (.cv s) (synCpw1 D))
      (synWrex y D (.classEq (.cv s) (synCsn (.cv y))))
      (.imp (.classEq (.cv p) (synCop (.cv u) (.cv s)))
        (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))
      p0009 p0029
  have p0031 :=
    @gRexlimiv (.classEq (.cv p) (synCop (.cv u) (.cv s)))
      (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))) s (synCpw1 D)
      dv_cache_0017 p0030
  have p0032 :=
    @gSyl (.classMem (.cv p) (synCxp (synCsn (.cv u)) (synCpw1 D)))
      (synWrex s (synCpw1 D) (.classEq (.cv p) (synCop (.cv u) (.cv s))))
      (synWrex x D (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))) p0008 p0031
  exact p0032


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecutinputdecode`. -/
@[expose]
noncomputable def gHncodecutinputdecode (x : Var) (u : Var) (A : Class) (p : Var)
    (_dv_A_p : p ∉ A.fv) (dv_A_u : u ∉ A.fv) (_dv_A_x : x ∉ A.fv) (dv_p_u : p ≠ u)
    (dv_p_x : p ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv p) (synChncodecutinputs A)) (synWrex u (synChwcn A)
          (synWrex x (synCfv (synC2nd) (.cv u))
            (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ ({ p } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let v : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_p : v ≠ p := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_q : y ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_q_ne_v : q ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_v_ne_q : v ≠ q := Ne.symm fresh_q_ne_v
  have dv_cache_0001 : y ∉ ((Class.cv p)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_p, not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_y, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synClnpwquoinputfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_q, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0008 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_v, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_u,
          not_false_eq_true])
  have dv_cache_0011 :
    u ∉
      ((Wff.classMem (.cv p)
          (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_p_u), fresh_u_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    v ∉
      ((Wff.imp (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
          (.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
                (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_q, fresh_v_ne_y,
          fresh_v_ne_p, fresh_v_not_A, fresh_v_ne_u, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0013 :
    q ∉
      ((Wff.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
              (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_y,
          fresh_q_not_A, fresh_q_ne_u, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((synWrex u (synChwcn A) (.classMem (.cv p)
            (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_p,
          fresh_y_ne_u, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCfv (synC2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0017 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show u ≠ x from (by exact dv_u_x))
  have p0000 := (Nominal.classEqRefl (synChncodecutinputs A))
  have p0001 :=
    @gEleq2i (synChncodecutinputs A)
      (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))) (.cv p) p0000
  have p0002 :=
    @gBiimpi (.classMem (.cv p) (synChncodecutinputs A))
      (.classMem (.cv p) (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      p0001
  have p0003 :=
    @gEluni y (.cv p) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))
      dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gSylib (.classMem (.cv p) (synChncodecutinputs A))
      (.classMem (.cv p) (synCuni (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (synWex y (synWa (.classMem (.cv p) (.cv y))
          (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))))
      p0002 p0003
  have p0005 :=
    @gSimpl (.classMem (.cv p) (.cv y))
      (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
  have p0006 :=
    @gSimpr (.classMem (.cv p) (.cv y))
      (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
  have p0007 := @gLnpwquoinputfnfn
  have p0008 := @gFnfun (synCvv) (synClnpwquoinputfn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gFvelima q (.cv y) (synCpw1 (synChwcn A)) (synClnpwquoinputfn) dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0011 :=
    @gMpan (synWfun (synClnpwquoinputfn))
      (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      p0009 p0010
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      p0006 p0011
  have p0013 := @gElpw1 v (.cv q) (synChwcn A) dv_cache_0006 dv_cache_0007
  have p0014 :=
    @gSimpl
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv p) (.cv y))
  have p0015 :=
    @gN3simpa (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
  have p0016 :=
    @gSimpl (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
  have p0017 :=
    @gSyl
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v))))
      (.classMem (.cv v) (synChwcn A)) p0015 p0016
  have p0018 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv v) (synChwcn A)) p0014 p0017
  have p0019 :=
    @gSimpr
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv p) (.cv y))
  have p0021 :=
    @gN3simpc (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
  have p0022 :=
    @gSimpr (.classEq (.cv q) (synCsn (.cv v)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
  have p0023 :=
    @gSyl
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (synWa (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)) p0021 p0022
  have p0024 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)) p0014 p0023
  have p0025 :=
    @gEqcomd
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y) p0024
  have p0028 :=
    @gSimpr (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
  have p0029 :=
    @gSyl
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v))))
      (.classEq (.cv q) (synCsn (.cv v))) p0015 p0028
  have p0030 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classEq (.cv q) (synCsn (.cv v))) p0014 p0029
  have p0031 := @gId (.classEq (.cv q) (synCsn (.cv v)))
  have p0032 :=
    @gFveq2d (.classEq (.cv q) (synCsn (.cv v))) (.cv q) (synCsn (.cv v))
      (synClnpwquoinputfn) p0031
  have p0033 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.classEq (.cv q) (synCsn (.cv v)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q))
        (synCfv (synClnpwquoinputfn) (synCsn (.cv v))))
      p0030 p0032
  have p0039 := @gLnpwquoinputfnvalhwcn v A dv_cache_0008
  have p0040 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synClnpwquoinputfn) (synCsn (.cv v)))
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0018 p0039
  have p0041 :=
    @gEqtrd
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (synCfv (synClnpwquoinputfn) (.cv q))
      (synCfv (synClnpwquoinputfn) (synCsn (.cv v)))
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) p0033 p0040
  have p0042 :=
    @gEqtrd
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.cv y) (synCfv (synClnpwquoinputfn) (.cv q))
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) p0025 p0041
  have p0043 :=
    @gEleqtrd
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.cv p) (.cv y) (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      p0019 p0042
  have p0044 :=
    @gJca
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv p) (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0018 p0043
  have p0045 := @gId (.classEq (.cv u) (.cv v))
  have p0046 := @gSneqd (.classEq (.cv u) (.cv v)) (.cv u) (.cv v) p0045
  have p0048 := @gFveq2d (.classEq (.cv u) (.cv v)) (.cv u) (.cv v) (synC2nd) p0045
  have p0049 := @gPw1eq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
  have p0050 :=
    @gSyl (.classEq (.cv u) (.cv v))
      (.classEq (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classEq (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv v))))
      p0048 p0049
  have p0051 :=
    @gXpeq12d (.classEq (.cv u) (.cv v)) (synCsn (.cv u)) (synCsn (.cv v))
      (synCpw1 (synCfv (synC2nd) (.cv u))) (synCpw1 (synCfv (synC2nd) (.cv v)))
      p0046 p0050
  have p0052 :=
    @gEleq2d (.classEq (.cv u) (.cv v))
      (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) (.cv p) p0051
  have p0053 :=
    @gRspcev
      (.classMem (.cv p) (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv p) (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      u (.cv v) (synChwcn A) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0052
  have p0054 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
          (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv p)
          (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (synWrex u (synChwcn A) (.classMem (.cv p)
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))
      p0044 p0053
  have p0055 :=
    @gEx
      (synW3a (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv p) (.cv y))
      (synWrex u (synChwcn A) (.classMem (.cv p)
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))
      p0054
  have p0056 :=
    @gN3exp (.classMem (.cv v) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv v)))
      (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
      (.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
            (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      p0055
  have p0057 :=
    @gRexlimiv (.classEq (.cv q) (synCsn (.cv v)))
      (.imp (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
        (.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
              (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))))
      v (synChwcn A) dv_cache_0012 p0056
  have p0058 :=
    @gSylbi (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synWrex v (synChwcn A) (.classEq (.cv q) (synCsn (.cv v))))
      (.imp (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
        (.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
              (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))))
      p0013 p0057
  have p0059 :=
    @gRexlimiv (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y))
      (.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
            (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      q (synCpw1 (synChwcn A)) dv_cache_0013 p0058
  have p0060 :=
    @gSyl
      (synWa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (synCfv (synClnpwquoinputfn) (.cv q)) (.cv y)))
      (.imp (.classMem (.cv p) (.cv y)) (synWrex u (synChwcn A) (.classMem (.cv p)
            (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))))
      p0012 p0059
  have p0061 :=
    @gMpd
      (synWa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (.classMem (.cv p) (.cv y))
      (synWrex u (synChwcn A) (.classMem (.cv p)
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))
      p0005 p0060
  have p0062 :=
    @gExlimiv
      (synWa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A)))))
      (synWrex u (synChwcn A) (.classMem (.cv p)
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))
      y dv_cache_0014 p0061
  have p0063 :=
    @gSyl (.classMem (.cv p) (synChncodecutinputs A))
      (synWex y (synWa (.classMem (.cv p) (.cv y))
          (.classMem (.cv y) (synCima (synClnpwquoinputfn) (synCpw1 (synChwcn A))))))
      (synWrex u (synChwcn A) (.classMem (.cv p)
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))
      p0004 p0062
  have p0064 :=
    @gHncodeinputproductdecode x u (synCfv (synC2nd) (.cv u)) p dv_cache_0015
      dv_cache_0016 dv_cache_0017
  have p0065 :=
    @gReximi
      (.classMem (.cv p) (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      u (synChwcn A) p0064
  have p0066 :=
    @gSyl (.classMem (.cv p) (synChncodecutinputs A))
      (synWrex u (synChwcn A) (.classMem (.cv p)
          (synCxp (synCsn (.cv u)) (synCpw1 (synCfv (synC2nd) (.cv u))))))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u))
          (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))
      p0063 p0065
  exact p0066

/-- Checked nominal proof certificate identified upstream as `g_hncodecutpairfnvalhwcn`. -/
@[expose]
noncomputable def gHncodecutpairfnvalhwcn (x : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classEq (synCfv (synChncodecutpairfn) (synCop (.cv u) (synCsn (.cv x)))) (synCop
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (.cv u)))) :=
  by
  have p0000 := @gHwcnpair u A
  have p0001 :=
    @gOpeq1d (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCsn (.cv x)) p0000
  have p0002 :=
    @gFveq2d (.classMem (.cv u) (synChwcn A)) (synCop (.cv u) (synCsn (.cv x)))
      (synCop (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synCsn (.cv x)))
      (synChncodecutpairfn) p0001
  have p0003 := @gFvex (.cv u) (synC1st)
  have p0004 := @gFvex (.cv u) (synC2nd)
  have p0005 :=
    @gHncodecutpairfnval x (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
      p0003 p0004
  have p0006 :=
    @gA1i
      (.classEq (synCfv (synChncodecutpairfn)
          (synCop (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
            (synCsn (.cv x)))) (synCop
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) p0005
  have p0008 :=
    @gEqcomd (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) p0000
  have p0009 :=
    @gOpeq2d (.classMem (.cv u) (synChwcn A))
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (.cv u)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      p0008
  have p0010 :=
    @gN3eqtrd (.classMem (.cv u) (synChwcn A))
      (synCfv (synChncodecutpairfn) (synCop (.cv u) (synCsn (.cv x))))
      (synCfv (synChncodecutpairfn)
        (synCop (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
          (synCsn (.cv x))))
      (synCop (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synCop (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (.cv u))
      p0002 p0006 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end
