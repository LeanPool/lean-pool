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

@[expose]
noncomputable def g_wppqkrelrescnvfunndv (A : Class) (B : Class)
    (_hyp_wppqkrelrescnvfunndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (_hyp_wppqkrelrescnvfunndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) :=
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
  have dv_cache_0002 : u ∉ ((syn_cxp A B)).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B)))
          (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B)))
          (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))).fv :=
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
  have dv_cache_0015 : v ∉ ((syn_cxp A B)).fv :=
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
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
              (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
          (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))).fv :=
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
      ((syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
              (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
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
      ((syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))).fv :=
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
      ((syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))).fv :=
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
      ((syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))).fv :=
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
    @g_simpl
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s))
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
  have p0001 :=
    @g_brcnv (.cv d) (.cv s)
      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0002 :=
    @g_brres (.cv s) (.cv d) (syn_ckqrel (syn_cwppqkrelkernel))
      (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
  have p0003 :=
    @g_bitri
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s))
      (syn_wbr (.cv s)
        (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (.cv d))
      (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      p0001 p0002
  have p0004 :=
    @g_biimpi
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s))
      (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s))
      (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      p0000 p0004
  have p0006 :=
    @g_simpr (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0005 p0006
  have p0008 := @g_elpw12 u (.cv s) (syn_cxp A B) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_biimpi (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) p0007
      p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
              (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
            (.cv t))) (.classMem (.cv u) (syn_cxp A B)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0012 :=
    @g_simpr
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (.classMem (.cv u) (syn_cxp A B))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
              (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
            (.cv t))) (.classMem (.cv u) (syn_cxp A B)))
      (.classMem (.cv u) (syn_cxp A B)) p0011 p0012
  have p0014 :=
    @g_elxp a b (.cv u) A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0015 :=
    @g_biimpi (.classMem (.cv u) (syn_cxp A B))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (.classMem (.cv u) (syn_cxp A B))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0013 p0015
  have p0017 :=
    @g_nfv
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      a dv_cache_0010
  have p0018 := @g_nfv (.classEq (.cv s) (.cv t)) a dv_cache_0011
  have p0019 :=
    @g_nfv
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      b dv_cache_0012
  have p0020 := @g_nfv (.classEq (.cv s) (.cv t)) b dv_cache_0013
  have p0021 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0023 :=
    @g_simpl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (.classMem (.cv u) (syn_cxp A B))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
              (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
            (.cv t))) (.classMem (.cv u) (syn_cxp A B)))
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      p0011 p0023
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      p0021 p0024
  have p0026 :=
    @g_simpr
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s))
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
  have p0027 :=
    @g_brcnv (.cv d) (.cv t)
      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0028 :=
    @g_brres (.cv t) (.cv d) (syn_ckqrel (syn_cwppqkrelkernel))
      (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
  have p0029 :=
    @g_bitri
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
      (syn_wbr (.cv t)
        (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (.cv d))
      (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      p0027 p0028
  have p0030 :=
    @g_biimpi
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
      (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      p0029
  have p0031 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t))
      (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      p0026 p0030
  have p0032 :=
    @g_simpr (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0033 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0031 p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0025 p0033
  have p0035 := @g_elpw12 v (.cv t) (syn_cxp A B) dv_cache_0014 dv_cache_0015
  have p0036 :=
    @g_biimpi (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wrex v (syn_cxp A B) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) p0035
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wrex v (syn_cxp A B) (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))) p0034
      p0036
  have p0038 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
              (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
          (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (syn_cxp A B)))
      (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0039 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (.cv v) (syn_cxp A B))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
              (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
          (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (syn_cxp A B)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      p0038 p0039
  have p0042 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
              (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
            (.cv t))) (.classMem (.cv u) (syn_cxp A B)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) p0021 p0042
  have p0044 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0045 :=
    @g_simpl (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
      (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) p0044 p0045
  have p0047 := @g_sneq (.cv u) (syn_cop (.cv a) (.cv b))
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
      (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))) p0046 p0047
  have p0049 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b))) p0048
  have p0050 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b))))
      p0043 p0049
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b))))) p0040 p0050
  have p0052 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
              (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
          (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (syn_cxp A B)))
      (.classEq (.cv t) (syn_csn (syn_csn (.cv v))))
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      p0040 p0025
  have p0068 :=
    @g_simpl (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0069 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wa (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0031 p0068
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0061 p0069
  have p0071 :=
    (Nominal.biimpRefl (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)))
  have p0072 :=
    @g_biimpi (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (syn_cop (.cv t) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0071
  have p0073 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (syn_cop (.cv t) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0070 p0072
  have p0075 :=
    @g_opeq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.cv t) (syn_csn (syn_csn (.cv v))) (.cv d) p0052
  have p0076 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_cop (.cv t) (.cv d)) (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d))
      (syn_ckqrel (syn_cwppqkrelkernel)) p0075
  have p0077 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.classMem (syn_cop (.cv t) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      p0073 p0076
  have p0092 :=
    @g_simpl (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0093 :=
    @g_syl
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wa (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
        (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0005 p0092
  have p0094 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)) p0025 p0093
  have p0095 :=
    (Nominal.biimpRefl (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)))
  have p0096 :=
    @g_biimpi (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0095
  have p0097 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) p0094 p0096
  have p0108 :=
    @g_opeq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d) p0050
  have p0109 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_cop (.cv s) (.cv d))
      (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
      (syn_ckqrel (syn_cwppqkrelkernel)) p0108
  have p0110 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      p0097 p0109
  have p0111 := @g_vex a
  have p0112 := @g_vex b
  have p0113 := @g_vex d
  have p0114 := @g_wppqkrelcanonicalfiberndv (.cv a) (.cv b) (.cv d) p0111 p0112 p0113
  have p0115 :=
    @g_biimpi
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (.cv d) (syn_copk (.cv a) (.cv b))) p0114
  have p0116 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (.cv d) (syn_copk (.cv a) (.cv b))) p0110 p0115
  have p0117 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv d) (syn_copk (.cv a) (.cv b))) p0040 p0116
  have p0118 :=
    @g_opeq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.cv d) (syn_copk (.cv a) (.cv b)) (syn_csn (syn_csn (.cv v))) p0117
  have p0119 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d))
      (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b)))
      (syn_ckqrel (syn_cwppqkrelkernel)) p0118
  have p0120 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b)))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      p0077 p0119
  have p0121 := @g_vex v
  have p0124 := @g_wppqkrelkernelpointbrndv (.cv v) (.cv a) (.cv b) p0121 p0111 p0112
  have p0125 :=
    @g_biimpi
      (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b)))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (.cv v) (syn_cop (.cv a) (.cv b))) p0124
  have p0126 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv v))) (syn_copk (.cv a) (.cv b)))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (.cv v) (syn_cop (.cv a) (.cv b))) p0120 p0125
  have p0127 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.cv v) (syn_cop (.cv a) (.cv b)) p0126
  have p0128 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (syn_csn (.cv v)) (syn_csn (syn_cop (.cv a) (.cv b))) p0127
  have p0129 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.cv t) (syn_csn (syn_csn (.cv v))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b))))
      p0052 p0128
  have p0130 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.cv t) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) p0129
  have p0131 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classMem (.cv u) (syn_cxp A B)))
              (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
            (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
          (.classMem (.cv v) (syn_cxp A B))) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv t) p0051 p0130
  have p0132 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
              (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
          (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
        (.classMem (.cv v) (syn_cxp A B)))
      (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))) (.classEq (.cv s) (.cv t)) p0131
  have p0133 :=
    @g_rexlimdva
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))) (.classEq (.cv s) (.cv t)) v
      (syn_cxp A B) dv_cache_0016 dv_cache_0017 p0132
  have p0134 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                  (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                    (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wrex v (syn_cxp A B) (.classEq (.cv t) (syn_csn (syn_csn (.cv v)))))
      (.classEq (.cv s) (.cv t)) p0037 p0133
  have p0135 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv s) (.cv t)) p0134
  have p0136 :=
    @g_exlimd
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv s) (.cv t)) b p0019 p0020 p0135
  have p0137 :=
    @g_exlimd
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv s) (.cv t)) a p0017 p0018 p0136
  have p0138 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                  (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      (.classEq (.cv s) (.cv t)) p0016 p0137
  have p0139 :=
    @g_ex
      (syn_wa (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
              (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
            (.cv t))) (.classMem (.cv u) (syn_cxp A B)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) (.classEq (.cv s) (.cv t)) p0138
  have p0140 :=
    @g_rexlimdva
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) (.classEq (.cv s) (.cv t)) u
      (syn_cxp A B) dv_cache_0018 dv_cache_0019 p0139
  have p0141 :=
    @g_mpd
      (syn_wa (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (.cv t)))
      (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (.classEq (.cv s) (.cv t)) p0010 p0140
  have p0142 := Nominal.gen p0141 t
  have p0143 := Nominal.gen p0142 s
  have p0144 := Nominal.gen p0143 d
  have p0145 :=
    @g_dffun2 d s t
      (syn_ccnv
        (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
  have p0146_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) (.all d (.all s (.all t (.imp (syn_wa
                  (syn_wbr (.cv d) (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d)
                    (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
                (.classEq (.cv s) (.cv t))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid
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
    @g_mpbir
      (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))))
      (.all d (.all s (.all t (.imp (syn_wa (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv s)) (syn_wbr (.cv d) (syn_ccnv
                    (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
                      (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (.cv t)))
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

@[expose]
noncomputable def g_wppqkrelrestypedenqkndv (A : Class) (B : Class)
    (hyp_wppqkrelresf1oqkndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppqkrelresf1oqkndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cqkrel (syn_cxp A B))) :=
  by
  have p0000 :=
    @g_wppqkrelresfnndv A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0001 :=
    @g_wppqkrelrescnvfunndv A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0002 := @g_wppqkrelresrangevalndv (syn_cxp A B)
  have p0003 :=
    @g_n_3pm3_2i
      (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wfun (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))))
      (.classEq (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B))))) (syn_cqkrel (syn_cxp A B)))
      p0000 p0001 p0002
  have p0004 :=
    @g_dff1o2 (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cqkrel (syn_cxp A B))
      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
  have p0005 :=
    @g_mpbir
      (syn_wf1o
        (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cqkrel (syn_cxp A B)))
      (syn_w3a (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
            (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) (syn_wfun
          (syn_ccnv (syn_cres (syn_ckqrel (syn_cwppqkrelkernel))
              (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))) (.classEq (syn_crn
            (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))))
          (syn_cqkrel (syn_cxp A B))))
      p0003 p0004
  have p0006 := @g_wppqkrelkernelexndv
  have p0007 := @g_kqrelex (syn_cwppqkrelkernel) p0006
  have p0008 := @g_xpex A B hyp_wppqkrelresf1oqkndv_1 hyp_wppqkrelresf1oqkndv_2
  have p0009 := @g_pw1ex (syn_cxp A B) p0008
  have p0010 := @g_pw1ex (syn_cpw1 (syn_cxp A B)) p0009
  have p0011 :=
    @g_resex (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))) p0007
      p0010
  have p0012 :=
    @g_f1oen (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cqkrel (syn_cxp A B))
      (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      p0011
  have p0013 := Nominal.mp p0005 p0012
  exact p0013

@[expose]
noncomputable def g_wppqkrelxprebasendv (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cqkrel (syn_cxp A B)) (syn_cxpk A B)) :=
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
  have dv_cache_0001 : x ∉ ((syn_cxp A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cxp A B)).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_cxp A B)).fv :=
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
  have dv_cache_0013 : z ∉ ((syn_cqkrel (syn_cxp A B))).fv :=
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
  have dv_cache_0014 : z ∉ ((syn_cxpk A B)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z
      (syn_cxp A B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @g_eleq2i (syn_cqkrel (syn_cxp A B))
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))))))
      (.cv z) p0000
  have p0002 :=
    @g_abid
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)))))
      z
  have p0003 :=
    @g_bitri (.classMem (.cv z) (syn_cqkrel (syn_cxp A B)))
      (.classMem (.cv z) (.cab z (syn_wex x (syn_wex y
              (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
                (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)))))
      p0001 p0002
  have p0004 := @g_opelxp (.cv x) (.cv y) A B
  have p0005 :=
    @g_anbi2i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) p0004
  have p0006 :=
    @g_n_2exbii
      (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
        (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)))
      (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      x y p0005
  have p0007 :=
    @g_bitri (.classMem (.cv z) (syn_cqkrel (syn_cxp A B)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      p0003 p0006
  have p0008 :=
    @g_elxpk x y (.cv z) A B dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0004
  have p0009 :=
    @g_bicomi (.classMem (.cv z) (syn_cxpk A B))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      p0008
  have p0010 :=
    @g_bitri (.classMem (.cv z) (syn_cqkrel (syn_cxp A B)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      (.classMem (.cv z) (syn_cxpk A B)) p0007 p0009
  have p0011 :=
    @g_eqriv z (syn_cqkrel (syn_cxp A B)) (syn_cxpk A B) dv_cache_0013 dv_cache_0014 p0010
  exact p0011

@[expose]
noncomputable def g_wppqkrelrestypedenndv (A : Class) (B : Class)
    (hyp_wppqkrelresf1ondv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppqkrelresf1ondv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cxpk A B)) :=
  by
  have p0000 :=
    @g_wppqkrelrestypedenqkndv A B hyp_wppqkrelresf1ondv_1 hyp_wppqkrelresf1ondv_2
  have p0001 := @g_wppqkrelxprebasendv A B
  have p0002 :=
    @g_breq2i (syn_cqkrel (syn_cxp A B)) (syn_cxpk A B)
      (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) p0001
  have p0003 :=
    @g_mpbi
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cqkrel (syn_cxp A B)))
      (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_cen) (syn_cxpk A B)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_hncardmonodndv (A : Class) (D : Class)
    (hyp_hncardmonodndv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hncardmonodndv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wss D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))) :=
  by
  have p0000 := @g_hncardeqdndv D (syn_cif (syn_wss D A) D (syn_c0))
  have p0001 :=
    @g_breq1d (.classEq D (syn_cif (syn_wss D A) D (syn_c0))) (syn_chncard D)
      (syn_chncard (syn_cif (syn_wss D A) D (syn_c0))) (syn_chncard A) (syn_clec) p0000
  have p0002 := @g_iftrue (syn_wss D A) D (syn_c0)
  have p0003 := @g_id (syn_wss D A)
  have p0004 :=
    @g_eqsstrd (syn_wss D A) (syn_cif (syn_wss D A) D (syn_c0)) D A p0002 p0003
  have p0005 := @g_iffalse (syn_wss D A) D (syn_c0)
  have p0006 := @g_n_0ss A
  have p0007 := @g_a1i (syn_wss (syn_c0) A) (.neg (syn_wss D A)) p0006
  have p0008 :=
    @g_eqsstrd (.neg (syn_wss D A)) (syn_cif (syn_wss D A) D (syn_c0)) (syn_c0) A p0005
      p0007
  have p0009 :=
    @g_pm2_61i (syn_wss D A) (syn_wss (syn_cif (syn_wss D A) D (syn_c0)) A) p0004 p0008
  have p0010 := @g_n_0ex
  have p0011 :=
    @g_pm3_2i (.classMem D (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) hyp_hncardmonodndv_1
      p0010
  have p0012 := @g_ifcl (syn_wss D A) D (syn_c0) (syn_cvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_hncardmono A (syn_cif (syn_wss D A) D (syn_c0)) p0009 p0013 hyp_hncardmonodndv_2
  have p0015 :=
    @g_dedth (syn_wss D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))
      (syn_wbr (syn_chncard (syn_cif (syn_wss D A) D (syn_c0))) (syn_clec) (syn_chncard A))
      D (syn_c0) p0001 p0014
  exact p0015

@[expose]
noncomputable def g_hncardf1leimpndv (A : Class) (D : Class) (F : Class)
    (hyp_hncardf1leimpndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (_hyp_hncardf1leimpndv_2 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hncardf1leimpndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wf1 F D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))) :=
  by
  have p0000 := @g_f1f1orn D A F
  have p0001 := @g_hncardf1oimpndv D (syn_crn F) F hyp_hncardf1leimpndv_1
  have p0002 :=
    @g_syl (syn_wf1 F D A) (syn_wf1o F D (syn_crn F))
      (.classEq (syn_chncard D) (syn_chncard (syn_crn F))) p0000 p0001
  have p0003 := @g_f1f D A F
  have p0004 := @g_frn D A F
  have p0005 := @g_syl (syn_wf1 F D A) (syn_wf F D A) (syn_wss (syn_crn F) A) p0003 p0004
  have p0006 := @g_rnex F hyp_hncardf1leimpndv_1
  have p0007 := @g_hncardmonodndv A (syn_crn F) p0006 hyp_hncardf1leimpndv_3
  have p0008 :=
    @g_syl (syn_wf1 F D A) (syn_wss (syn_crn F) A)
      (syn_wbr (syn_chncard (syn_crn F)) (syn_clec) (syn_chncard A)) p0005 p0007
  have p0009 :=
    @g_eqbrtrd (syn_wf1 F D A) (syn_chncard D) (syn_chncard (syn_crn F)) (syn_chncard A)
      (syn_clec) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_hncardnclecndv (A : Class) (D : Class)
    (hyp_hncardnclecndv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hncardnclecndv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A))
        (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))) :=
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
  have dv_cache_0003 : f ∉ ((syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))).fv :=
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
    @g_nclenc D A f dv_cache_0001 dv_cache_0002 hyp_hncardnclecndv_1 hyp_hncardnclecndv_2
  have p0001 :=
    @g_biimpi (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A))
      (syn_wex f (syn_wf1 (.cv f) D A)) p0000
  have p0002 := @g_vex f
  have p0003 :=
    @g_hncardf1leimpndv A D (.cv f) p0002 hyp_hncardnclecndv_1 hyp_hncardnclecndv_2
  have p0004 :=
    @g_exlimiv (syn_wf1 (.cv f) D A) (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))
      f dv_cache_0003 p0003
  have p0005 :=
    @g_syl (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A)) (syn_wex f (syn_wf1 (.cv f) D A))
      (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A)) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_hnordcardnclecndv (A : Class) (D : Class)
    (hyp_hnordcardnclecndv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnordcardnclecndv_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A))
        (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A)))) :=
  by
  have p0000 := @g_hncardnclecndv A D hyp_hnordcardnclecndv_1 hyp_hnordcardnclecndv_2
  have p0001 := (Nominal.classEqRefl (syn_chncard D))
  have p0002 := (Nominal.classEqRefl (syn_chncard A))
  have p0003 :=
    @g_breq12i (syn_chncard D) (syn_cnc (syn_chnord D)) (syn_chncard A)
      (syn_cnc (syn_chnord A)) (syn_clec) p0001 p0002
  have p0004 :=
    @g_biimpi (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))
      (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) p0003
  have p0005 :=
    @g_syl (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc A))
      (syn_wbr (syn_chncard D) (syn_clec) (syn_chncard A))
      (syn_wbr (syn_cnc (syn_chnord D)) (syn_clec) (syn_cnc (syn_chnord A))) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wppqkrelliteralenndv (X : Class)
    (hyp_wppqkrelliteralenndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (syn_wbr (syn_cxp (syn_cxpk X X) (syn_cnnc)) (syn_cen)
        (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc))) :=
  by
  have p0000 :=
    @g_wppqkrelrestypedenndv X X hyp_wppqkrelliteralenndv_1 hyp_wppqkrelliteralenndv_1
  have p0001 := @g_ensym (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cxpk X X)
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cen) (syn_cxpk X X))
      (syn_wbr (syn_cxpk X X) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp X X)))) p0000 p0001
  have p0003 := @g_nncex
  have p0004 := @g_enrflx (syn_cnnc) p0003
  have p0005 :=
    @g_pm3_2i (syn_wbr (syn_cxpk X X) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp X X))))
      (syn_wbr (syn_cnnc) (syn_cen) (syn_cnnc)) p0002 p0004
  have p0006 :=
    @g_xpen (syn_cxpk X X) (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc) (syn_cnnc)
  have p0007 := Nominal.mp p0005 p0006
  exact p0007

@[expose]
noncomputable def g_wppqkrelliteralnceqndv (X : Class)
    (hyp_wppqkrelliteralnceqndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))
        (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc)))) :=
  by
  have p0000 := @g_wppqkrelliteralenndv X hyp_wppqkrelliteralnceqndv_1
  have p0001 := @g_xpkex X X hyp_wppqkrelliteralnceqndv_1 hyp_wppqkrelliteralnceqndv_1
  have p0002 := @g_nncex
  have p0003 := @g_xpex (syn_cxpk X X) (syn_cnnc) p0001 p0002
  have p0004 :=
    @g_eqnc (syn_cxp (syn_cxpk X X) (syn_cnnc))
      (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc)) p0003
  have p0005 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cxp (syn_cxpk X X) (syn_cnnc)))
        (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc))))
      (syn_wbr (syn_cxp (syn_cxpk X X) (syn_cnnc)) (syn_cen)
        (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp X X))) (syn_cnnc)))
      p0000 p0004
  exact p0005

@[expose]
noncomputable def g_hnordlnquoeq (A : Class) (R : Class) (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_hnordlnquoeq_1 : Nominal.NPrf (.classEq (syn_clnker R) (syn_chwniso A))) :
    Nominal.NPrf (.classEq (syn_clnquo R (syn_chwcn A)) (syn_chnord A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_clnquo R (syn_chwcn A)))
  have p0001 := @g_qseq2 (syn_clnker R) (syn_chwniso A) (syn_chwcn A)
  have p0002 := Nominal.mp hyp_hnordlnquoeq_1 p0001
  have p0003 :=
    @g_eqtri (syn_clnquo R (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_clnker R))
      (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_chnord A))
  have p0005 := @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0004
  have p0006 :=
    @g_eqtri (syn_clnquo R (syn_chwcn A)) (syn_cqs (syn_chwcn A) (syn_chwniso A))
      (syn_chnord A) p0003 p0005
  exact p0006

@[expose]
noncomputable def g_hnordwefromcmp (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv)
    (hyp_hnordwefromcmp_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_hnordwefromcmp_2 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hnordwefromcmp_3 :
      Nominal.NPrf (.classMem (syn_cop R (syn_chwcn A)) (syn_clnpwc (syn_chwcn A))))
    (hyp_hnordwefromcmp_4 : Nominal.NPrf (.classEq (syn_clnker R) (syn_chwniso A))) :
    Nominal.NPrf (syn_wbr (syn_clnqord R (syn_chwcn A)) (syn_cwe) (syn_chnord A)) :=
  by
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv (R).fv := by
    exact
      (show Disjoint ((syn_chwcn A)).fv (R).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn];
          exact (show Disjoint (A).fv (R).fv from (by exact dv_A_R))))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 := @g_hwcnexg A
  have p0001 := Nominal.mp hyp_hnordwefromcmp_1 p0000
  have p0002 :=
    @g_lnworigqordwe (syn_chwcn A) R dv_cache_0001 p0001 hyp_hnordwefromcmp_2
      hyp_hnordwefromcmp_3
  have p0003 := @g_hnordlnquoeq A R dv_cache_0002 hyp_hnordwefromcmp_4
  have p0004 :=
    @g_breq2i (syn_clnquo R (syn_chwcn A)) (syn_chnord A) (syn_clnqord R (syn_chwcn A))
      (syn_cwe) p0003
  have p0005 :=
    @g_mpbi (syn_wbr (syn_clnqord R (syn_chwcn A)) (syn_cwe) (syn_clnquo R (syn_chwcn A)))
      (syn_wbr (syn_clnqord R (syn_chwcn A)) (syn_cwe) (syn_chnord A)) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_hncodecutfnfn : Nominal.NPrf (syn_wfn (syn_chncodecutfn) (syn_cvv)) :=
  by
  have p0000 := @g_lninteropfn
  have p0001 := @g_ln1stfn
  have p0003 := @g_fncovv (syn_c1st) (syn_c1st) p0001 p0001
  have p0004 := @g_fncross
  have p0006 := @g_ln2ndfn
  have p0008 := @g_fncovv (syn_c2nd) (syn_c1st) p0006 p0001
  have p0009 := @g_lnimageopfn
  have p0010 := @g_imageswapfn
  have p0011 := @g_fnlndifop
  have p0015 := @g_idex
  have p0016 := @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0003 p0017
  have p0019 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @g_inidm (syn_cvv)
  have p0022 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0021
  have p0023 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv))
      p0020 p0022
  have p0024 :=
    @g_fncovv (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0011 p0023
  have p0025 := (Nominal.classEqRefl (syn_chncodestrictfn))
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      p0025
  have p0027 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv))
      p0024 p0026
  have p0028 := @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0010 p0027
  have p0030 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0028 p0006
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
      (syn_c2nd)
  have p0032 := Nominal.mp p0030 p0031
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0021
  have p0035 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cvv))
      p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0009 p0035
  have p0037 := (Nominal.classEqRefl (syn_chncodepredfn))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
        (syn_cvv))
      p0036 p0038
  have p0040 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0008 p0039
  have p0041 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0042 := Nominal.mp p0040 p0041
  have p0044 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0021
  have p0045 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv))
      p0042 p0044
  have p0046 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0000 p0045
  have p0047 := (Nominal.classEqRefl (syn_chncodecarrierfn))
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      p0047
  have p0049 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv))
      p0046 p0048
  have p0095 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0049 p0049
  have p0096 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0097 := Nominal.mp p0095 p0096
  have p0099 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0021
  have p0100 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0097
      p0099
  have p0101 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0004
      p0100
  have p0102 := (Nominal.classEqRefl (syn_chncodesquarefn))
  have p0103 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      p0102
  have p0104 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
        (syn_cvv))
      p0101 p0103
  have p0105 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0003 p0104
  have p0106 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0107 := Nominal.mp p0105 p0106
  have p0109 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0021
  have p0110 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv))
      p0107 p0109
  have p0111 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0000 p0110
  have p0112 := (Nominal.classEqRefl (syn_chncoderelfn))
  have p0113 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      p0112
  have p0114 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv))
      p0111 p0113
  have p0160 :=
    @g_pm3_2i (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0114 p0049
  have p0161 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncoderelfn) (syn_chncodecarrierfn)
  have p0162 := Nominal.mp p0160 p0161
  have p0164 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0021
  have p0165 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0162 p0164
  have p0166 := (Nominal.classEqRefl (syn_chncodecutfn))
  have p0167 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutfn)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0166
  have p0168 :=
    @g_mpbir (syn_wfn (syn_chncodecutfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0165 p0167
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

@[expose]
noncomputable def g_hncodecutpairfnfn :
    Nominal.NPrf (syn_wfn (syn_chncodecutpairfn) (syn_cvv)) :=
  by
  have p0000 := @g_lninteropfn
  have p0001 := @g_ln1stfn
  have p0003 := @g_fncovv (syn_c1st) (syn_c1st) p0001 p0001
  have p0004 := @g_fncross
  have p0006 := @g_ln2ndfn
  have p0008 := @g_fncovv (syn_c2nd) (syn_c1st) p0006 p0001
  have p0009 := @g_lnimageopfn
  have p0010 := @g_imageswapfn
  have p0011 := @g_fnlndifop
  have p0015 := @g_idex
  have p0016 := @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0003 p0017
  have p0019 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @g_inidm (syn_cvv)
  have p0022 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0021
  have p0023 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv))
      p0020 p0022
  have p0024 :=
    @g_fncovv (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0011 p0023
  have p0025 := (Nominal.classEqRefl (syn_chncodestrictfn))
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      p0025
  have p0027 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv))
      p0024 p0026
  have p0028 := @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0010 p0027
  have p0030 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0028 p0006
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
      (syn_c2nd)
  have p0032 := Nominal.mp p0030 p0031
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0021
  have p0035 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cvv))
      p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0009 p0035
  have p0037 := (Nominal.classEqRefl (syn_chncodepredfn))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
        (syn_cvv))
      p0036 p0038
  have p0040 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0008 p0039
  have p0041 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0042 := Nominal.mp p0040 p0041
  have p0044 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0021
  have p0045 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv))
      p0042 p0044
  have p0046 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0000 p0045
  have p0047 := (Nominal.classEqRefl (syn_chncodecarrierfn))
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      p0047
  have p0049 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv))
      p0046 p0048
  have p0095 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0049 p0049
  have p0096 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0097 := Nominal.mp p0095 p0096
  have p0099 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0021
  have p0100 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0097
      p0099
  have p0101 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0004
      p0100
  have p0102 := (Nominal.classEqRefl (syn_chncodesquarefn))
  have p0103 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      p0102
  have p0104 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
        (syn_cvv))
      p0101 p0103
  have p0105 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0003 p0104
  have p0106 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0107 := Nominal.mp p0105 p0106
  have p0109 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0021
  have p0110 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv))
      p0107 p0109
  have p0111 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0000 p0110
  have p0112 := (Nominal.classEqRefl (syn_chncoderelfn))
  have p0113 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      p0112
  have p0114 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv))
      p0111 p0113
  have p0160 :=
    @g_pm3_2i (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0114 p0049
  have p0161 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncoderelfn) (syn_chncodecarrierfn)
  have p0162 := Nominal.mp p0160 p0161
  have p0164 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0021
  have p0165 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0162 p0164
  have p0166 := (Nominal.classEqRefl (syn_chncodecutfn))
  have p0167 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutfn)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0166
  have p0168 :=
    @g_mpbir (syn_wfn (syn_chncodecutfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0165 p0167
  have p0170 :=
    @g_pm3_2i (syn_wfn (syn_chncodecutfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) p0168
      p0001
  have p0171 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecutfn) (syn_c1st)
  have p0172 := Nominal.mp p0170 p0171
  have p0174 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncodecutfn) (syn_c1st)) p0021
  have p0175 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cvv)) p0172 p0174
  have p0176 := (Nominal.classEqRefl (syn_chncodecutpairfn))
  have p0177 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutpairfn) (syn_ctxp (syn_chncodecutfn) (syn_c1st))
      p0176
  have p0178 :=
    @g_mpbir (syn_wfn (syn_chncodecutpairfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cvv)) p0175 p0177
  exact p0178

@[expose]
noncomputable def g_hncodecutpairfnex :
    Nominal.NPrf (.classMem (syn_chncodecutpairfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodecutpairfn))
  have p0001 := (Nominal.classEqRefl (syn_chncodecutfn))
  have p0002 := (Nominal.classEqRefl (syn_chncoderelfn))
  have p0003 := @g_lninteropex
  have p0004 := @g_n_1stex
  have p0006 := @g_coex (syn_c1st) (syn_c1st) p0004 p0004
  have p0007 := (Nominal.classEqRefl (syn_chncodesquarefn))
  have p0008 := @g_crossex
  have p0009 := (Nominal.classEqRefl (syn_chncodecarrierfn))
  have p0011 := @g_n_2ndex
  have p0013 := @g_coex (syn_c2nd) (syn_c1st) p0011 p0004
  have p0014 := (Nominal.classEqRefl (syn_chncodepredfn))
  have p0015 := @g_lnimageopex
  have p0016 := @g_swapex
  have p0017 := @g_imageex (syn_cswap) p0016
  have p0018 := (Nominal.classEqRefl (syn_chncodestrictfn))
  have p0019 := @g_lndifopex
  have p0023 := @g_vvex
  have p0024 := @g_snex (syn_cid)
  have p0025 := @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0023 p0024
  have p0026 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
      p0006 p0025
  have p0027 :=
    @g_coex (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0019 p0026
  have p0028 :=
    @g_eqeltri (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      (syn_cvv) p0018 p0027
  have p0029 := @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0017 p0028
  have p0031 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0029
      p0011
  have p0032 :=
    @g_coex (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0015 p0031
  have p0033 :=
    @g_eqeltri (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      (syn_cvv) p0014 p0032
  have p0034 := @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0013 p0033
  have p0035 :=
    @g_coex (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0003 p0034
  have p0036 :=
    @g_eqeltri (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      (syn_cvv) p0009 p0035
  have p0065 := @g_txpex (syn_chncodecarrierfn) (syn_chncodecarrierfn) p0036 p0036
  have p0066 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0008
      p0065
  have p0067 :=
    @g_eqeltri (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      (syn_cvv) p0007 p0066
  have p0068 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn) p0006 p0067
  have p0069 :=
    @g_coex (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0003 p0068
  have p0070 :=
    @g_eqeltri (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      (syn_cvv) p0002 p0069
  have p0099 := @g_txpex (syn_chncoderelfn) (syn_chncodecarrierfn) p0070 p0036
  have p0100 :=
    @g_eqeltri (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
      (syn_cvv) p0001 p0099
  have p0102 := @g_txpex (syn_chncodecutfn) (syn_c1st) p0100 p0004
  have p0103 :=
    @g_eqeltri (syn_chncodecutpairfn) (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cvv)
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

@[expose]
noncomputable def g_hncodecutfnval (x : Var) (D : Class) (R : Class)
    (hyp_hncodecutfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hncodecutfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_chnwcutcode R D (.cv x))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodecutfn))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutfn)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0000
  have p0002 := @g_lninteropfn
  have p0003 := @g_ln1stfn
  have p0005 := @g_fncovv (syn_c1st) (syn_c1st) p0003 p0003
  have p0006 := @g_fncross
  have p0008 := @g_ln2ndfn
  have p0010 := @g_fncovv (syn_c2nd) (syn_c1st) p0008 p0003
  have p0011 := @g_lnimageopfn
  have p0012 := @g_imageswapfn
  have p0013 := @g_fnlndifop
  have p0017 := @g_idex
  have p0018 := @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0005 p0019
  have p0021 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @g_inidm (syn_cvv)
  have p0024 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0023
  have p0025 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv))
      p0022 p0024
  have p0026 :=
    @g_fncovv (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0013 p0025
  have p0027 := (Nominal.classEqRefl (syn_chncodestrictfn))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv))
      p0026 p0028
  have p0030 := @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0012 p0029
  have p0032 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0030 p0008
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
      (syn_c2nd)
  have p0034 := Nominal.mp p0032 p0033
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0023
  have p0037 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cvv))
      p0034 p0036
  have p0038 :=
    @g_fncovv (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0011 p0037
  have p0039 := (Nominal.classEqRefl (syn_chncodepredfn))
  have p0040 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      p0039
  have p0041 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
        (syn_cvv))
      p0038 p0040
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0010 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0023
  have p0047 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv))
      p0044 p0046
  have p0048 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0002 p0047
  have p0049 := (Nominal.classEqRefl (syn_chncodecarrierfn))
  have p0050 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      p0049
  have p0051 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv))
      p0048 p0050
  have p0097 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0051 p0051
  have p0098 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0099 := Nominal.mp p0097 p0098
  have p0101 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0023
  have p0102 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0099
      p0101
  have p0103 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0006
      p0102
  have p0104 := (Nominal.classEqRefl (syn_chncodesquarefn))
  have p0105 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      p0104
  have p0106 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
        (syn_cvv))
      p0103 p0105
  have p0107 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0005 p0106
  have p0108 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0109 := Nominal.mp p0107 p0108
  have p0111 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0023
  have p0112 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv))
      p0109 p0111
  have p0113 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0002 p0112
  have p0114 := (Nominal.classEqRefl (syn_chncoderelfn))
  have p0115 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      p0114
  have p0116 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv))
      p0113 p0115
  have p0162 := @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0163 := @g_snex (.cv x)
  have p0164 := @g_opex (syn_cop R D) (syn_csn (.cv x)) p0162 p0163
  have p0165 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncoderelfn)
      (syn_chncodecarrierfn) p0116 p0051 p0164
  have p0167 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      p0114
  have p0281 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0112 p0164
  have p0282 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
  have p0283 := Nominal.mp p0281 p0282
  have p0391 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_chncodesquarefn) p0005 p0106 p0164
  have p0396 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0003 p0164
  have p0397 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c1st) (syn_c1st)
  have p0398 := Nominal.mp p0396 p0397
  have p0401 := @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0162 p0163
  have p0402 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D)
      (syn_c1st) p0401
  have p0403 := @g_opfv1st R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0404 :=
    @g_eqtri
      (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_c1st) (syn_cop R D)) R p0402 p0403
  have p0405 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      R p0398 p0404
  have p0407 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      p0104
  have p0507 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0102 p0164
  have p0508 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccross)
      (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
  have p0509 := Nominal.mp p0507 p0508
  have p0603 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecarrierfn)
      (syn_chncodecarrierfn) p0051 p0051 p0164
  have p0605 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      p0049
  have p0649 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0047 p0164
  have p0650 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
  have p0651 := Nominal.mp p0649 p0650
  have p0689 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c2nd) (syn_c1st))
      (syn_chncodepredfn) p0010 p0041 p0164
  have p0695 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c2nd) (syn_c1st)
  have p0696 := Nominal.mp p0396 p0695
  have p0700 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D)
      (syn_c2nd) p0401
  have p0701 := @g_opfv2nd R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0702 :=
    @g_eqtri
      (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_c2nd) (syn_cop R D)) D p0700 p0701
  have p0703 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      D p0696 p0702
  have p0705 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      p0039
  have p0735 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0037 p0164
  have p0736 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
  have p0737 := Nominal.mp p0735 p0736
  have p0761 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x)))
      (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0030 p0008
      p0164
  have p0782 :=
    @g_pm3_2i (syn_wfn (syn_chncodestrictfn) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0029 p0164
  have p0783 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cimage (syn_cswap))
      (syn_chncodestrictfn)
  have p0784 := Nominal.mp p0782 p0783
  have p0786 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      p0027
  have p0802 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0025 p0164
  have p0803 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
  have p0804 := Nominal.mp p0802 p0803
  have p0814 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0005 p0019 p0164
  have p0833 :=
    @g_fvconst2 (syn_cvv) (syn_cid) (syn_cop (syn_cop R D) (syn_csn (.cv x))) p0017
  have p0834 := Nominal.mp p0164 p0833
  have p0835 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      R
      (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cid) p0405 p0834
  have p0836 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop R (syn_cid)) p0814 p0835
  have p0837 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop R (syn_cid)) (syn_clndifop) p0836
  have p0838 := (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_cid)))
  have p0839 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_cid))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) p0838
  have p0841 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) hyp_hncodecutfnval_1
      p0017
  have p0842 := @g_lndifopvalg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0843 := Nominal.mp p0841 p0842
  have p0844 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop R (syn_cid)))
      (syn_co R (syn_clndifop) (syn_cid)) (syn_cdif R (syn_cid)) p0839 p0843
  have p0845 :=
    @g_eqtri
      (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_cdif R (syn_cid)) p0837 p0844
  have p0846 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cdif R (syn_cid)) p0804 p0845
  have p0847 :=
    @g_eqtri (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cdif R (syn_cid)) p0786 p0846
  have p0848 :=
    @g_fveq2i (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cdif R (syn_cid)) (syn_cimage (syn_cswap)) p0847
  have p0850 := @g_difex R (syn_cid) hyp_hncodecutfnval_1 p0017
  have p0851 := @g_wppimageswapfv (syn_cdif R (syn_cid)) p0850
  have p0852 :=
    @g_eqtri
      (syn_cfv (syn_cimage (syn_cswap))
        (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cdif R (syn_cid)))
      (syn_ccnv (syn_cdif R (syn_cid))) p0848 p0851
  have p0853 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_cimage (syn_cswap))
        (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_ccnv (syn_cdif R (syn_cid))) p0784 p0852
  have p0856 := @g_opfv2nd (syn_cop R D) (syn_csn (.cv x)) p0162 p0163
  have p0857 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_csn (.cv x))
      p0853 p0856
  have p0858 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0761 p0857
  have p0859 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_clnimageop) p0858
  have p0862 := @g_cnvex (syn_cdif R (syn_cid)) p0850
  have p0864 :=
    @g_lnimageopval (syn_csn (.cv x)) (syn_ccnv (syn_cdif R (syn_cid))) p0862 p0163
  have p0865 :=
    @g_eqtri
      (syn_cfv (syn_clnimageop) (syn_cfv
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0859 p0864
  have p0866 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_clnimageop) (syn_cfv
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0737 p0865
  have p0867 :=
    @g_eqtri (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0705 p0866
  have p0868 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      D (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0703 p0867
  have p0869 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st))
          (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0689
      p0868
  have p0870 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_clninterop) p0869
  have p0875 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0862 p0163
  have p0876 :=
    @g_lninteropval D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      hyp_hncodecutfnval_2 p0875
  have p0877 :=
    @g_eqtri
      (syn_cfv (syn_clninterop)
        (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_clninterop)
        (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0870
      p0876
  have p0878 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_clninterop)
        (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0651
      p0877
  have p0879 :=
    @g_eqtri (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0605
      p0878
  have p1156 :=
    @g_opeq12i (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0879
      p0879
  have p1157 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0603 p1156
  have p1158 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_ccross) p1157
  have p1159 :=
    (Nominal.classEqRefl
      (syn_co (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_ccross)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p1160 :=
    @g_eqcomi
      (syn_co (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_ccross) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cfv (syn_ccross) (syn_cop
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p1159
  have p1166 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      hyp_hncodecutfnval_2 p0875
  have p1173 :=
    @g_pm3_2i
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p1166 p1166
  have p1174 :=
    @g_ovcross (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)
      (syn_cvv)
  have p1175 := Nominal.mp p1173 p1174
  have p1176 :=
    @g_eqtri
      (syn_cfv (syn_ccross) (syn_cop
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_co (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_ccross) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p1160 p1175
  have p1177 :=
    @g_eqtri
      (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_ccross) (syn_cop
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p1158 p1176
  have p1178 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0509 p1177
  have p1179 :=
    @g_eqtri (syn_cfv (syn_chncodesquarefn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0407 p1178
  have p1180 :=
    @g_opeq12i
      (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      R (syn_cfv (syn_chncodesquarefn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0405 p1179
  have p1181 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_chncodesquarefn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0391 p1180
  have p1182 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_clninterop) p1181
  have p1195 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1166
      p1166
  have p1196 :=
    @g_lninteropval R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      hyp_hncodecutfnval_1 p1195
  have p1197 :=
    @g_eqtri
      (syn_cfv (syn_clninterop)
        (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cfv (syn_clninterop) (syn_cop R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p1182 p1196
  have p1198 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_clninterop)
        (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
          (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0283 p1197
  have p1199 :=
    @g_eqtri (syn_cfv (syn_chncoderelfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0167 p1198
  have p1476 :=
    @g_opeq12i (syn_cfv (syn_chncoderelfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1199
      p0879
  have p1477 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_chncoderelfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0165 p1476
  have p1478 :=
    @g_eqtri (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0001 p1477
  have p1479 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p1480 :=
    @g_eqcomi (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p1479
  have p1481 :=
    @g_eqtri (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_chnwcutcode R D (.cv x)) p1478 p1480
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

@[expose]
noncomputable def g_hncodecutpairfnval (x : Var) (D : Class) (R : Class)
    (hyp_hncodecutpairfnval_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hncodecutpairfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodecutpairfn))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutpairfn)
      (syn_ctxp (syn_chncodecutfn) (syn_c1st)) p0000
  have p0002 := @g_lninteropfn
  have p0003 := @g_ln1stfn
  have p0005 := @g_fncovv (syn_c1st) (syn_c1st) p0003 p0003
  have p0006 := @g_fncross
  have p0008 := @g_ln2ndfn
  have p0010 := @g_fncovv (syn_c2nd) (syn_c1st) p0008 p0003
  have p0011 := @g_lnimageopfn
  have p0012 := @g_imageswapfn
  have p0013 := @g_fnlndifop
  have p0017 := @g_idex
  have p0018 := @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0005 p0019
  have p0021 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @g_inidm (syn_cvv)
  have p0024 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0023
  have p0025 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv))
      p0022 p0024
  have p0026 :=
    @g_fncovv (syn_clndifop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
      p0013 p0025
  have p0027 := (Nominal.classEqRefl (syn_chncodestrictfn))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn)
      (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_cxp (syn_cvv) (syn_csn (syn_cid)))))
      p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv))
      p0026 p0028
  have p0030 := @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0012 p0029
  have p0032 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv))
      (syn_wfn (syn_c2nd) (syn_cvv)) p0030 p0008
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn))
      (syn_c2nd)
  have p0034 := Nominal.mp p0032 p0033
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0023
  have p0037 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
        (syn_cvv))
      p0034 p0036
  have p0038 :=
    @g_fncovv (syn_clnimageop)
      (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
      p0011 p0037
  have p0039 := (Nominal.classEqRefl (syn_chncodepredfn))
  have p0040 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn)
      (syn_ccom (syn_clnimageop)
        (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
      p0039
  have p0041 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageop)
          (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)))
        (syn_cvv))
      p0038 p0040
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0010 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0023
  have p0047 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv))
      p0044 p0046
  have p0048 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0002 p0047
  have p0049 := (Nominal.classEqRefl (syn_chncodecarrierfn))
  have p0050 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)))
      p0049
  have p0051 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv))
      p0048 p0050
  have p0097 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0051 p0051
  have p0098 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0099 := Nominal.mp p0097 p0098
  have p0101 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0023
  have p0102 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0099
      p0101
  have p0103 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0006
      p0102
  have p0104 := (Nominal.classEqRefl (syn_chncodesquarefn))
  have p0105 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn)
      (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
      p0104
  have p0106 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)))
        (syn_cvv))
      p0103 p0105
  have p0107 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv))
      (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0005 p0106
  have p0108 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0109 := Nominal.mp p0107 p0108
  have p0111 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0023
  have p0112 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv))
      p0109 p0111
  have p0113 :=
    @g_fncovv (syn_clninterop)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0002 p0112
  have p0114 := (Nominal.classEqRefl (syn_chncoderelfn))
  have p0115 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn)
      (syn_ccom (syn_clninterop)
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)))
      p0114
  have p0116 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clninterop)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv))
      p0113 p0115
  have p0162 :=
    @g_pm3_2i (syn_wfn (syn_chncoderelfn) (syn_cvv))
      (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0116 p0051
  have p0163 := @g_fntxp (syn_cvv) (syn_cvv) (syn_chncoderelfn) (syn_chncodecarrierfn)
  have p0164 := Nominal.mp p0162 p0163
  have p0166 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0023
  have p0167 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0164 p0166
  have p0168 := (Nominal.classEqRefl (syn_chncodecutfn))
  have p0169 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutfn)
      (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0168
  have p0170 :=
    @g_mpbir (syn_wfn (syn_chncodecutfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0167 p0169
  have p0172 := @g_opex R D hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0173 := @g_snex (.cv x)
  have p0174 := @g_opex (syn_cop R D) (syn_csn (.cv x)) p0172 p0173
  have p0175 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutfn) (syn_c1st)
      p0170 p0003 p0174
  have p0176 := @g_hncodecutfnval x D R hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0179 := @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0172 p0173
  have p0180 :=
    @g_opeq12i (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_chnwcutcode R D (.cv x))
      (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) p0176
      p0179
  have p0181 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_chncodecutfn) (syn_c1st))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))))
      (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) p0175 p0180
  have p0182 :=
    @g_eqtri (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cfv (syn_ctxp (syn_chncodecutfn) (syn_c1st))
        (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) p0001 p0181
  exact p0182

@[expose]
noncomputable def g_hncodecmpsetexg (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncodecmpset A))
  have p0001 := @g_hwnisoexg A
  have p0002 := (Nominal.classEqRefl (syn_chncodecutrel A))
  have p0003 := @g_hncodecutpairfnex
  have p0004 :=
    @g_a1i (.classMem (syn_chncodecutpairfn) (syn_cvv)) (.classMem A (syn_cvv)) p0003
  have p0005 := (Nominal.classEqRefl (syn_chncodecutinputs A))
  have p0006 := @g_lnpwquoinputfnex
  have p0007 :=
    @g_a1i (.classMem (syn_clnpwquoinputfn) (syn_cvv)) (.classMem A (syn_cvv)) p0006
  have p0008 := @g_hwcnexg A
  have p0009 := @g_pw1exg (syn_chwcn A) (syn_cvv)
  have p0010 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_clnpwquoinputfn) (syn_cvv))
      (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0007 p0010
  have p0012 :=
    @g_imaexg (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_clnpwquoinputfn) (syn_cvv))
        (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)))
      (.classMem (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv))
      p0011 p0012
  have p0014 :=
    @g_uniexg (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv)
  have p0015 :=
    @g_syl (.classMem A (syn_cvv))
      (.classMem (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv))
      (.classMem (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_cvv))
      p0013 p0014
  have p0016 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncodecutinputs A)
      (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_cvv) p0005
      p0015
  have p0017 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecutpairfn) (syn_cvv))
      (.classMem (syn_chncodecutinputs A) (syn_cvv)) p0004 p0016
  have p0018 :=
    @g_imaexg (syn_chncodecutpairfn) (syn_chncodecutinputs A) (syn_cvv) (syn_cvv)
  have p0019 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chncodecutpairfn) (syn_cvv))
        (.classMem (syn_chncodecutinputs A) (syn_cvv)))
      (.classMem (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_cvv))
      p0017 p0018
  have p0020 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncodecutrel A)
      (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_cvv) p0002 p0019
  have p0022 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecutrel A) (syn_cvv))
      (.classMem (syn_chwniso A) (syn_cvv)) p0020 p0001
  have p0023 := @g_coexg (syn_chncodecutrel A) (syn_chwniso A) (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chncodecutrel A) (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)))
      (.classMem (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv)) p0022 p0023
  have p0025 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv))
      (.classMem (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv)) p0001 p0024
  have p0026 :=
    @g_unexg (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv)
      (syn_cvv)
  have p0027 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwniso A) (syn_cvv))
        (.classMem (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv)))
      (.classMem (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)))
        (syn_cvv))
      p0025 p0026
  have p0028 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncodecmpset A)
      (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (syn_cvv)
      p0000 p0027
  exact p0028

@[expose]
noncomputable def g_brhncodecmpset (x : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex x
            (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x))
              (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v)))))) :=
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
  have dv_cache_0003 : x ∉ ((syn_chncodecutrel A)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_chwniso A)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_chncodecmpset A))
  have p0001 :=
    @g_breqi (.cv u) (.cv v) (syn_chncodecmpset A)
      (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) p0000
  have p0002 :=
    @g_brun (.cv u) (.cv v) (syn_chwniso A)
      (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))
  have p0003 :=
    @g_brco x (.cv u) (.cv v) (syn_chncodecutrel A) (syn_chwniso A) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_orbi2i (syn_wbr (.cv u) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (.cv v))
      (syn_wex x (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x))
          (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0003
  have p0005 :=
    @g_bitri
      (syn_wbr (.cv u)
        (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv u) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (.cv v)))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex x
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x))
            (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v)))))
      p0002 p0004
  have p0006 :=
    @g_bitri (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (.cv u)
        (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex x
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x))
            (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v)))))
      p0001 p0005
  exact p0006

@[expose]
noncomputable def g_hncodecutinputmemi (x : Var) (A : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_hncodecutinputmemi_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hncodecutinputmemi_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
        (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutinputs A))) :=
  by
  have p0000 := @g_opex R D hyp_hncodecutinputmemi_1 hyp_hncodecutinputmemi_2
  have p0001 := @g_snid (syn_cop R D) p0000
  have p0002 :=
    @g_a1i (.classMem (syn_cop R D) (syn_csn (syn_cop R D)))
      (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0001
  have p0003 := @g_simpr (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)
  have p0004 := @g_snelpw1 (.cv x) D
  have p0005 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (syn_cop R D) (syn_csn (syn_cop R D)))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0002 p0005
  have p0007 :=
    @g_opelxp (syn_cop R D) (syn_csn (.cv x)) (syn_csn (syn_cop R D)) (syn_cpw1 D)
  have p0008 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (syn_wa (.classMem (syn_cop R D) (syn_csn (syn_cop R D)))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 D)))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      p0006 p0007
  have p0009 := @g_lnpwquoinputfnval D R hyp_hncodecutinputmemi_1 hyp_hncodecutinputmemi_2
  have p0010 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
        (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0009
  have p0011 := @g_simpl (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)
  have p0012 := @g_snelpw1 (syn_cop R D) (syn_chwcn A)
  have p0013 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (syn_cop R D) (syn_chwcn A))
      (.classMem (syn_csn (syn_cop R D)) (syn_cpw1 (syn_chwcn A))) p0011 p0012
  have p0014 := @g_lnpwquoinputfnfn
  have p0015 := @g_fnfun (syn_cvv) (syn_clnpwquoinputfn)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_snex (syn_cop R D)
  have p0019 := @g_fndm (syn_cvv) (syn_clnpwquoinputfn)
  have p0020 := Nominal.mp p0014 p0019
  have p0021 :=
    @g_eleqtrri (syn_csn (syn_cop R D)) (syn_cvv) (syn_cdm (syn_clnpwquoinputfn)) p0017
      p0020
  have p0022 :=
    @g_pm3_2i (syn_wfun (syn_clnpwquoinputfn))
      (.classMem (syn_csn (syn_cop R D)) (syn_cdm (syn_clnpwquoinputfn))) p0016 p0021
  have p0023 :=
    @g_funfvima (syn_cpw1 (syn_chwcn A)) (syn_csn (syn_cop R D)) (syn_clnpwquoinputfn)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (syn_csn (syn_cop R D)) (syn_cpw1 (syn_chwcn A)))
      (.classMem (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
        (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
      p0013 p0024
  have p0026 :=
    @g_eqeltrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))
      (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
      (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) p0010 p0025
  have p0027 :=
    @g_jca (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x)))
        (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
      (.classMem (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
        (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
      p0008 p0026
  have p0028 :=
    @g_elunii (syn_cop (syn_cop R D) (syn_csn (.cv x)))
      (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
      (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))
  have p0029 :=
    @g_syl (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (syn_wa (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x)))
          (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))
        (.classMem (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))
          (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x)))
        (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      p0027 p0028
  have p0030 := (Nominal.classEqRefl (syn_chncodecutinputs A))
  have p0031 :=
    @g_a1i
      (.classEq (syn_chncodecutinputs A)
        (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0030
  have p0032 :=
    @g_eleqtrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (syn_cop (syn_cop R D) (syn_csn (.cv x)))
      (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
      (syn_chncodecutinputs A) p0029 p0031
  exact p0032

@[expose]
noncomputable def g_hncodecutreledgei (x : Var) (A : Class) (D : Class) (R : Class)
    (dv_A_R : Disjoint A.fv R.fv)
    (hyp_hncodecutreledgei_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_hncodecutreledgei_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
        (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chncodecutrel A) (syn_cop R D))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_hncodecutpairfnval x D R hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0001 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)))
      (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0000
  have p0002 :=
    @g_hncodecutinputmemi x A D R dv_cache_0001 hyp_hncodecutreledgei_1
      hyp_hncodecutreledgei_2
  have p0003 := @g_hncodecutpairfnfn
  have p0004 := @g_fnfun (syn_cvv) (syn_chncodecutpairfn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_opex R D hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0007 := @g_snex (.cv x)
  have p0008 := @g_opex (syn_cop R D) (syn_csn (.cv x)) p0006 p0007
  have p0010 := @g_fndm (syn_cvv) (syn_chncodecutpairfn)
  have p0011 := Nominal.mp p0003 p0010
  have p0012 :=
    @g_eleqtrri (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)
      (syn_cdm (syn_chncodecutpairfn)) p0008 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfun (syn_chncodecutpairfn))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cdm (syn_chncodecutpairfn)))
      p0005 p0012
  have p0014 :=
    @g_funfvima (syn_chncodecutinputs A) (syn_cop (syn_cop R D) (syn_csn (.cv x)))
      (syn_chncodecutpairfn)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutinputs A))
      (.classMem (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
        (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)))
      p0002 p0015
  have p0017 :=
    @g_eqeltrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))
      (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D))
      (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) p0001 p0016
  have p0018 := (Nominal.classEqRefl (syn_chncodecutrel A))
  have p0019 :=
    @g_a1i
      (.classEq (syn_chncodecutrel A)
        (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)))
      (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @g_eleqtrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D))
      (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_chncodecutrel A)
      p0017 p0019
  have p0021 :=
    (Nominal.biimpRefl
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chncodecutrel A) (syn_cop R D)))
  have p0022 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D))
      (.classMem (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) (syn_chncodecutrel A))
      (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chncodecutrel A) (syn_cop R D)) p0020
      p0021
  exact p0022

@[expose]
noncomputable def g_lnpwquoinputfnvalhwcn (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv u)))
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) :=
  by
  have p0000 := @g_hwcnpair u A
  have p0001 :=
    @g_sneqd (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_csn (.cv u))
      (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_clnpwquoinputfn) p0001
  have p0003 := @g_fvex (.cv u) (syn_c1st)
  have p0004 := @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_lnpwquoinputfnval (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0003
      p0004
  have p0006 :=
    @g_a1i
      (.classEq (syn_cfv (syn_clnpwquoinputfn)
          (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cxp (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) p0005
  have p0009 :=
    @g_xpeq1d (.classMem (.cv u) (syn_chwcn A)) (syn_csn (.cv u))
      (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0001
  have p0010 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn A))
      (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      p0009
  have p0011 :=
    @g_n_3eqtrd (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv u)))
      (syn_cfv (syn_clnpwquoinputfn)
        (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cxp (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0002 p0006
      p0010
  exact p0011

@[expose]
noncomputable def g_hncodeinputproductdecode (x : Var) (u : Var) (D : Class) (p : Var)
    (dv_D_x : x ∉ D.fv) (dv_p_x : p ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 D)))
        (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) :=
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
  have dv_cache_0003 : w ∉ ((syn_csn (.cv u))).fv :=
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
  have dv_cache_0004 : s ∉ ((syn_csn (.cv u))).fv :=
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
  have dv_cache_0005 : w ∉ ((syn_cpw1 D)).fv :=
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
  have dv_cache_0006 : s ∉ ((syn_cpw1 D)).fv :=
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
    w ∉ ((syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))).fv :=
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
    x ∉ ((Wff.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y))))).fv :=
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
      ((Wff.imp (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
          (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))).fv :=
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
    s ∉ ((syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))).fv :=
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
    @g_elxp2 w s (.cv p) (syn_csn (.cv u)) (syn_cpw1 D) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @g_vex u
  have p0002 := @g_id (.classEq (.cv w) (.cv u))
  have p0003 := @g_opeq1d (.classEq (.cv w) (.cv u)) (.cv w) (.cv u) (.cv s) p0002
  have p0004 :=
    @g_eqeq2d (.classEq (.cv w) (.cv u)) (syn_cop (.cv w) (.cv s))
      (syn_cop (.cv u) (.cv s)) (.cv p) p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv w) (.cv u)) (.classEq (.cv p) (syn_cop (.cv w) (.cv s)))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) s (syn_cpw1 D) dv_cache_0008 p0004
  have p0006 :=
    @g_rexsn (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv w) (.cv s))))
      (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) w (.cv u)
      dv_cache_0009 dv_cache_0010 p0001 p0005
  have p0007 :=
    @g_biimpi
      (syn_wrex w (syn_csn (.cv u))
        (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv w) (.cv s)))))
      (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) p0006
  have p0008 :=
    @g_sylbi (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 D)))
      (syn_wrex w (syn_csn (.cv u))
        (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv w) (.cv s)))))
      (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) p0000 p0007
  have p0009 := @g_elpw1 y (.cv s) D dv_cache_0011 dv_cache_0012
  have p0010 :=
    @g_n_3simpa (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0011 := @g_simpl (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
  have p0012 :=
    @g_syl
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (syn_wa (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))))
      (.classMem (.cv y) D) p0010 p0011
  have p0013 :=
    @g_n_3simpc (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0014 :=
    @g_simpr (.classEq (.cv s) (syn_csn (.cv y)))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0015 :=
    @g_syl
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (syn_wa (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) p0013 p0014
  have p0017 :=
    @g_simpl (.classEq (.cv s) (syn_csn (.cv y)))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0018 :=
    @g_syl
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (syn_wa (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (.classEq (.cv s) (syn_csn (.cv y))) p0013 p0017
  have p0019 :=
    @g_opeq2d
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (.cv s) (syn_csn (.cv y)) (.cv u) p0018
  have p0020 :=
    @g_eqtrd
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (.cv p) (syn_cop (.cv u) (.cv s)) (syn_cop (.cv u) (syn_csn (.cv y))) p0015 p0019
  have p0021 :=
    @g_jca
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (.classMem (.cv y) D) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y)))) p0012
      p0020
  have p0022 := @g_id (.classEq (.cv x) (.cv y))
  have p0023 := @g_sneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0022
  have p0024 :=
    @g_opeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv u) p0023
  have p0025 :=
    @g_eqeq2d (.classEq (.cv x) (.cv y)) (syn_cop (.cv u) (syn_csn (.cv x)))
      (syn_cop (.cv u) (syn_csn (.cv y))) (.cv p) p0024
  have p0026 :=
    @g_rspcev (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
      (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y)))) x (.cv y) D dv_cache_0013
      dv_cache_0014 dv_cache_0015 p0025
  have p0027 :=
    @g_syl
      (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
        (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (syn_wa (.classMem (.cv y) D) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y)))))
      (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) p0021 p0026
  have p0028 :=
    @g_n_3exp (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
      (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
      (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) p0027
  have p0029 :=
    @g_rexlimiv (.classEq (.cv s) (syn_csn (.cv y)))
      (.imp (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
        (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))
      y D dv_cache_0016 p0028
  have p0030 :=
    @g_sylbi (.classMem (.cv s) (syn_cpw1 D))
      (syn_wrex y D (.classEq (.cv s) (syn_csn (.cv y))))
      (.imp (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
        (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))
      p0009 p0029
  have p0031 :=
    @g_rexlimiv (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
      (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) s (syn_cpw1 D)
      dv_cache_0017 p0030
  have p0032 :=
    @g_syl (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 D)))
      (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))
      (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) p0008 p0031
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

@[expose]
noncomputable def g_hncodecutinputdecode (x : Var) (u : Var) (A : Class) (p : Var)
    (_dv_A_p : p ∉ A.fv) (dv_A_u : u ∉ A.fv) (_dv_A_x : x ∉ A.fv) (dv_p_u : p ≠ u)
    (dv_p_x : p ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv p) (syn_chncodecutinputs A)) (syn_wrex u (syn_chwcn A)
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))) :=
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
    y ∉ ((syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))).fv :=
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
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv :=
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
  have dv_cache_0005 : q ∉ ((syn_clnpwquoinputfn)).fv :=
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
  have dv_cache_0007 : v ∉ ((syn_chwcn A)).fv :=
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
  have dv_cache_0010 : u ∉ ((syn_chwcn A)).fv :=
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
          (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))).fv :=
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
      ((Wff.imp (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
          (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
                (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))))).fv :=
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
      ((Wff.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
              (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
      ((syn_wrex u (syn_chwcn A) (.classMem (.cv p)
            (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_chncodecutinputs A))
  have p0001 :=
    @g_eleq2i (syn_chncodecutinputs A)
      (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (.cv p) p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv p) (syn_chncodecutinputs A))
      (.classMem (.cv p) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      p0001
  have p0003 :=
    @g_eluni y (.cv p) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))
      dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_sylib (.classMem (.cv p) (syn_chncodecutinputs A))
      (.classMem (.cv p) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (syn_wex y (syn_wa (.classMem (.cv p) (.cv y))
          (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))))
      p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (.cv p) (.cv y))
      (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
  have p0006 :=
    @g_simpr (.classMem (.cv p) (.cv y))
      (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
  have p0007 := @g_lnpwquoinputfnfn
  have p0008 := @g_fnfun (syn_cvv) (syn_clnpwquoinputfn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_fvelima q (.cv y) (syn_cpw1 (syn_chwcn A)) (syn_clnpwquoinputfn) dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0011 :=
    @g_mpan (syn_wfun (syn_clnpwquoinputfn))
      (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      p0009 p0010
  have p0012 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      p0006 p0011
  have p0013 := @g_elpw1 v (.cv q) (syn_chwcn A) dv_cache_0006 dv_cache_0007
  have p0014 :=
    @g_simpl
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv p) (.cv y))
  have p0015 :=
    @g_n_3simpa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0016 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
  have p0017 :=
    @g_syl
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))))
      (.classMem (.cv v) (syn_chwcn A)) p0015 p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv v) (syn_chwcn A)) p0014 p0017
  have p0019 :=
    @g_simpr
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv p) (.cv y))
  have p0021 :=
    @g_n_3simpc (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0022 :=
    @g_simpr (.classEq (.cv q) (syn_csn (.cv v)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
  have p0023 :=
    @g_syl
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (syn_wa (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) p0021 p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)) p0014 p0023
  have p0025 :=
    @g_eqcomd
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y) p0024
  have p0028 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
  have p0029 :=
    @g_syl
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v))))
      (.classEq (.cv q) (syn_csn (.cv v))) p0015 p0028
  have p0030 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classEq (.cv q) (syn_csn (.cv v))) p0014 p0029
  have p0031 := @g_id (.classEq (.cv q) (syn_csn (.cv v)))
  have p0032 :=
    @g_fveq2d (.classEq (.cv q) (syn_csn (.cv v))) (.cv q) (syn_csn (.cv v))
      (syn_clnpwquoinputfn) p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.classEq (.cv q) (syn_csn (.cv v)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q))
        (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv v))))
      p0030 p0032
  have p0039 := @g_lnpwquoinputfnvalhwcn v A dv_cache_0008
  have p0040 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv v)))
        (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0018 p0039
  have p0041 :=
    @g_eqtrd
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (syn_cfv (syn_clnpwquoinputfn) (.cv q))
      (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv v)))
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0033 p0040
  have p0042 :=
    @g_eqtrd
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.cv y) (syn_cfv (syn_clnpwquoinputfn) (.cv q))
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0025 p0041
  have p0043 :=
    @g_eleqtrd
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.cv p) (.cv y) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      p0019 p0042
  have p0044 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      p0018 p0043
  have p0045 := @g_id (.classEq (.cv u) (.cv v))
  have p0046 := @g_sneqd (.classEq (.cv u) (.cv v)) (.cv u) (.cv v) p0045
  have p0048 := @g_fveq2d (.classEq (.cv u) (.cv v)) (.cv u) (.cv v) (syn_c2nd) p0045
  have p0049 := @g_pw1eq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
  have p0050 :=
    @g_syl (.classEq (.cv u) (.cv v))
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))
      p0048 p0049
  have p0051 :=
    @g_xpeq12d (.classEq (.cv u) (.cv v)) (syn_csn (.cv u)) (syn_csn (.cv v))
      (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
      p0046 p0050
  have p0052 :=
    @g_eleq2d (.classEq (.cv u) (.cv v))
      (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.cv p) p0051
  have p0053 :=
    @g_rspcev
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))
      u (.cv v) (syn_chwcn A) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0052
  have p0054 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
          (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
        (.classMem (.cv p) (.cv y)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv v)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))))
      (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      p0044 p0053
  have p0055 :=
    @g_ex
      (syn_w3a (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.classMem (.cv p) (.cv y))
      (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      p0054
  have p0056 :=
    @g_n_3exp (.classMem (.cv v) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv v)))
      (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
      (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
            (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      p0055
  have p0057 :=
    @g_rexlimiv (.classEq (.cv q) (syn_csn (.cv v)))
      (.imp (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
        (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
              (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))))
      v (syn_chwcn A) dv_cache_0012 p0056
  have p0058 :=
    @g_sylbi (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
      (syn_wrex v (syn_chwcn A) (.classEq (.cv q) (syn_csn (.cv v))))
      (.imp (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
        (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
              (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))))
      p0013 p0057
  have p0059 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y))
      (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
            (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      q (syn_cpw1 (syn_chwcn A)) dv_cache_0013 p0058
  have p0060 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (syn_wrex q (syn_cpw1 (syn_chwcn A))
        (.classEq (syn_cfv (syn_clnpwquoinputfn) (.cv q)) (.cv y)))
      (.imp (.classMem (.cv p) (.cv y)) (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
            (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))
      p0012 p0059
  have p0061 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (.classMem (.cv p) (.cv y))
      (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      p0005 p0060
  have p0062 :=
    @g_exlimiv
      (syn_wa (.classMem (.cv p) (.cv y))
        (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))))
      (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      y dv_cache_0014 p0061
  have p0063 :=
    @g_syl (.classMem (.cv p) (syn_chncodecutinputs A))
      (syn_wex y (syn_wa (.classMem (.cv p) (.cv y))
          (.classMem (.cv y) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))))
      (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      p0004 p0062
  have p0064 :=
    @g_hncodeinputproductdecode x u (syn_cfv (syn_c2nd) (.cv u)) p dv_cache_0015
      dv_cache_0016 dv_cache_0017
  have p0065 :=
    @g_reximi
      (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      u (syn_chwcn A) p0064
  have p0066 :=
    @g_syl (.classMem (.cv p) (syn_chncodecutinputs A))
      (syn_wrex u (syn_chwcn A) (.classMem (.cv p)
          (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))
      p0063 p0065
  exact p0066

@[expose]
noncomputable def g_hncodecutpairfnvalhwcn (x : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (.cv u)))) :=
  by
  have p0000 := @g_hwcnpair u A
  have p0001 :=
    @g_opeq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_csn (.cv x)) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_cop (.cv u) (syn_csn (.cv x)))
      (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_csn (.cv x)))
      (syn_chncodecutpairfn) p0001
  have p0003 := @g_fvex (.cv u) (syn_c1st)
  have p0004 := @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_hncodecutpairfnval x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
      p0003 p0004
  have p0006 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chncodecutpairfn)
          (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_csn (.cv x)))) (syn_cop
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcn A)) p0005
  have p0008 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0009 :=
    @g_opeq2d (.classMem (.cv u) (syn_chwcn A))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (.cv u)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      p0008
  have p0010 :=
    @g_n_3eqtrd (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x))))
      (syn_cfv (syn_chncodecutpairfn)
        (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_csn (.cv x))))
      (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (.cv u))
      p0002 p0006 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end
