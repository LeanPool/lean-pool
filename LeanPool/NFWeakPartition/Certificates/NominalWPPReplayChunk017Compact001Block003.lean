/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppfdpivrangencdlitraw (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_wppfdpivrangencdlitraw_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_wppfdpivrangencdlitraw_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppfdpivrangencdlitraw_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec)
          (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let h : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  let f : Var := freshVar proofSupport 6
  let g : Var := freshVar proofSupport 7
  let z : Var := freshVar proofSupport 8
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have fresh_v_ne_k : v ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_k_ne_v : k ≠ v := Ne.symm fresh_v_ne_k
  have fresh_v_ne_y : v ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_h : v ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_h_ne_v : h ≠ v := Ne.symm fresh_v_ne_h
  have fresh_v_ne_t : v ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_v : t ≠ v := Ne.symm fresh_v_ne_t
  have fresh_v_ne_f : v ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_f_ne_v : f ≠ v := Ne.symm fresh_v_ne_f
  have fresh_v_ne_g : v ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_g_ne_v : g ≠ v := Ne.symm fresh_v_ne_g
  have fresh_v_ne_z : v ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_u_ne_k : u ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_u : k ≠ u := Ne.symm fresh_u_ne_k
  have fresh_u_ne_y : u ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_h : u ≠ h :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_h_ne_u : h ≠ u := Ne.symm fresh_u_ne_h
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have fresh_u_ne_f : u ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_ne_g : u ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_g_ne_u : g ≠ u := Ne.symm fresh_u_ne_g
  have fresh_u_ne_z : u ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_k_ne_y : k ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_h : k ≠ h :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_h_ne_k : h ≠ k := Ne.symm fresh_k_ne_h
  have fresh_k_ne_t : k ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_y_ne_h : y ≠ h :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_h_ne_t : h ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_h_ne_f : h ≠ f :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_f_ne_h : f ≠ h := Ne.symm fresh_h_ne_f
  have fresh_h_ne_g : h ≠ g :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_g_ne_h : g ≠ h := Ne.symm fresh_h_ne_g
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_g_ne_z : g ≠ z :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv v)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({ v } : Finset Var)) from
              (Finset.disjoint_union_left.mpr
                ⟨(Finset.disjoint_union_left.mpr
                    ⟨(show Disjoint ((A).fv) (({ v } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show v ∉ (A).fv from (by exact fresh_v_not_A)))),
                      (show Disjoint ((B).fv) (({ v } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show v ∉ (B).fv from (by exact fresh_v_not_B))))⟩),
                  (show Disjoint ((R).fv) (({ v } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show v ∉ (R).fv from (by exact fresh_v_not_R))))⟩))))
  have dv_cache_0005 : Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({ u } : Finset Var)) from
              (Finset.disjoint_union_left.mpr
                ⟨(Finset.disjoint_union_left.mpr
                    ⟨(show Disjoint ((A).fv) (({ u } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show u ∉ (A).fv from (by exact fresh_u_not_A)))),
                      (show Disjoint ((B).fv) (({ u } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show u ∉ (B).fv from (by exact fresh_u_not_B))))⟩),
                  (show Disjoint ((R).fv) (({ u } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show u ∉ (R).fv from (by exact fresh_u_not_R))))⟩))))
  have dv_cache_0006 : y ∉ ((syn_cfdpivmap2 R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 : Disjoint ((Class.cv v)).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv v)).fv ((Class.cv u)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (v),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (u)];
          exact
            (show Disjoint (({ v } : Finset Var)) (({ u } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show v ∉ ({ u } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show v ≠ u from (by exact fresh_v_ne_u))))))))
  have dv_cache_0008 : y ∉ ((Class.cv v)).fv :=
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
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_cfdpivmap2 R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
          Finset.mem_union, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_cfdpivmap2 R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
          Finset.mem_union, fresh_v_not_A, fresh_v_not_B, fresh_v_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_cfdpivmap2 R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
          Finset.mem_union, fresh_u_not_A, fresh_u_not_B, fresh_u_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0013 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0014 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0015 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0016 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0017 : v ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0018 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0019 : z ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_v, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_u, not_false_eq_true])
  have dv_cache_0021 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0022 : g ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0023 : g ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show g ≠ u from (by exact fresh_g_ne_u))
  have dv_cache_0024 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0025 : g ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show g ≠ z from (by exact fresh_g_ne_z))
  have dv_cache_0026 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0027 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0028 :
    Disjoint
      ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv
      ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (show Disjoint ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv ((syn_cvv)).fv
        from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact
            (show
              Disjoint
                ((((syn_cxp (.cv v) (syn_csn (syn_c0c)))).fv) ∪
                  (((syn_cxp (.cv u)
                      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))).fv))
                ((∅ : Finset Var))
              from
              (Finset.disjoint_union_left.mpr
                ⟨(show
                    Disjoint (((syn_cxp (.cv v) (syn_csn (syn_c0c)))).fv)
                      ((∅ : Finset Var))
                    from (by simp)),
                  (show
                    Disjoint
                      (((syn_cxp (.cv u)
                          (syn_crab y (syn_cnnc)
                            (.neg (.classEq (.cv y) (syn_c0c)))))).fv)
                      ((∅ : Finset Var))
                    from (by simp))⟩))))
  have dv_cache_0029 :
    f ∉
      ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_u, fresh_f_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0030 :
    g ∉
      ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_g_ne_v, fresh_g_ne_u, fresh_g_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 :
    h ∉
      ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_h_ne_v, fresh_h_ne_u, fresh_h_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 : Disjoint ((syn_cxp (.cv u) (syn_cnnc))).fv ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (show Disjoint ((syn_cxp (.cv u) (syn_cnnc))).fv ((syn_cvv)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact
            (show Disjoint ((((Class.cv u)).fv) ∪ (((syn_cnnc)).fv)) ((∅ : Finset Var))
              from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((Class.cv u)).fv) ((∅ : Finset Var)) from (by simp)),
                  (show Disjoint (((syn_cnnc)).fv) ((∅ : Finset Var)) from (by simp))⟩))))
  have dv_cache_0033 : f ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0034 : g ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0035 : h ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0036 : Disjoint ((syn_cvv)).fv ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (show Disjoint ((syn_cvv)).fv ((syn_cvv)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact (show Disjoint ((∅ : Finset Var)) ((∅ : Finset Var)) from (by simp))))
  have dv_cache_0037 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have dv_cache_0038 : f ≠ h :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact (show f ≠ h from (by exact fresh_f_ne_h))
  have dv_cache_0039 : g ≠ h :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show g ≠ h from (by exact fresh_g_ne_h))
  have dv_cache_0040 : t ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show t ≠ v from (by exact fresh_t_ne_v))
  have dv_cache_0041 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0042 : t ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (show t ≠ y from (by exact fresh_t_ne_y))
  have dv_cache_0043 : h ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_v, not_false_eq_true])
  have dv_cache_0044 : k ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_v, not_false_eq_true])
  have dv_cache_0045 : t ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_v, not_false_eq_true])
  have dv_cache_0046 :
    k ∉
      ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_k_ne_v, fresh_k_ne_u, fresh_k_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0047 :
    t ∉
      ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_t_ne_v, fresh_t_ne_u, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0048 : k ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0049 : t ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0050 : h ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact (show h ≠ k from (by exact fresh_h_ne_k))
  have dv_cache_0051 : h ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show h ≠ t from (by exact fresh_h_ne_t))
  have dv_cache_0052 : k ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (show k ≠ t from (by exact fresh_k_ne_t))
  have dv_cache_0053 : u ∉ ((syn_cxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_u_not_B, or_false, not_false_eq_true])
  have dv_cache_0054 :
    u ∉
      ((Wff.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
            (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp)
            (syn_wbr (syn_cnc (.cv v)) (syn_clec)
              (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, fresh_u_not_A, fresh_u_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0055 : v ∉ ((syn_cfdpivrange2 R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          Finset.mem_union, fresh_v_not_A, fresh_v_not_B, fresh_v_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0056 :
    v ∉
      ((Wff.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
            (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp)
            (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec)
              (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_A, fresh_v_not_R, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_eqid (syn_cxpk B B)
  have p0001 := @g_eqid (syn_cfdpivrange2 R A B)
  have p0002 :=
    @g_pm3_2i (.classEq (syn_cxpk B B) (syn_cxpk B B))
      (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B)) p0000 p0001
  have p0003 :=
    @g_fdpivrange2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2
      hyp_wppfdpivrangencdlitraw_3
  have p0004 :=
    @g_biidd (.classEq (.cv v) (syn_cfdpivrange2 R A B))
      (.classEq (syn_cxpk B B) (syn_cxpk B B))
  have p0005 := @g_id (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0006 :=
    @g_eqeq1d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.cv v) (syn_cfdpivrange2 R A B)
      (syn_cfdpivrange2 R A B) p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv v) (syn_cfdpivrange2 R A B))
      (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (syn_cxpk B B) (syn_cxpk B B))
      (.classEq (.cv v) (syn_cfdpivrange2 R A B))
      (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B)) p0004 p0006
  have p0008 := @g_biidd (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_wwpp)
  have p0010 :=
    @g_nceqd (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.cv v) (syn_cfdpivrange2 R A B)
      p0005
  have p0011 :=
    @g_breq1d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_cnc (.cv v))
      (syn_cnc (syn_cfdpivrange2 R A B)) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))
      (syn_clec) p0010
  have p0012 :=
    @g_imbi12d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_wwpp) (syn_wwpp)
      (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))
      (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec)
        (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))
      p0008 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv v) (syn_cfdpivrange2 R A B))
      (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
        (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
        (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B)))
      (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec)
          (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))))
      (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec)
          (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))))
      p0007 p0012
  have p0014 := @g_xpkex B B hyp_wppfdpivrangencdlitraw_3 hyp_wppfdpivrangencdlitraw_3
  have p0015 := @g_id (.classEq (.cv u) (syn_cxpk B B))
  have p0016 :=
    @g_eqeq1d (.classEq (.cv u) (syn_cxpk B B)) (.cv u) (syn_cxpk B B) (syn_cxpk B B)
      p0015
  have p0017 :=
    @g_biidd (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0018 :=
    @g_anbi12d (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv u) (syn_cxpk B B))
      (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
      (.classEq (.cv v) (syn_cfdpivrange2 R A B)) p0016 p0017
  have p0019 := @g_biidd (.classEq (.cv u) (syn_cxpk B B)) (syn_wwpp)
  have p0021 :=
    @g_xpeq1d (.classEq (.cv u) (syn_cxpk B B)) (.cv u) (syn_cxpk B B) (syn_cnnc) p0015
  have p0022 :=
    @g_nceqd (.classEq (.cv u) (syn_cxpk B B)) (syn_cxp (.cv u) (syn_cnnc))
      (syn_cxp (syn_cxpk B B) (syn_cnnc)) p0021
  have p0023 :=
    @g_breq2d (.classEq (.cv u) (syn_cxpk B B)) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))
      (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))) (syn_cnc (.cv v)) (syn_clec) p0022
  have p0024 :=
    @g_imbi12d (.classEq (.cv u) (syn_cxpk B B)) (syn_wwpp) (syn_wwpp)
      (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc))))
      (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))
      p0019 p0023
  have p0025 :=
    @g_imbi12d (.classEq (.cv u) (syn_cxpk B B))
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
        (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (.imp (syn_wwpp)
        (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))))
      (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec)
          (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))))
      p0018 p0024
  have p0026 :=
    @g_fdpivmap2onto A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2
      hyp_wppfdpivrangencdlitraw_3
  have p0027 :=
    @g_a1i (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B))
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      p0026
  have p0028 :=
    @g_simpl (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0029 :=
    @g_foeq2 (.cv u) (syn_cxpk B B) (syn_cfdpivrange2 R A B) (syn_cfdpivmap2 R A B)
  have p0030 :=
    @g_syl
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (.classEq (.cv u) (syn_cxpk B B))
      (syn_wb (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B))
        (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)))
      p0028 p0029
  have p0031 :=
    @g_mpbird
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B))
      (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) p0027 p0030
  have p0032 :=
    @g_simpr (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0033 := @g_foeq3 (.cv v) (syn_cfdpivrange2 R A B) (.cv u) (syn_cfdpivmap2 R A B)
  have p0034 :=
    @g_syl
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (.classEq (.cv v) (syn_cfdpivrange2 R A B))
      (syn_wb (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (.cv v))
        (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B)))
      p0032 p0033
  have p0035 :=
    @g_mpbird
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (.cv v))
      (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B)) p0031 p0034
  have p0036 :=
    @g_wpppadonto y (syn_cfdpivmap2 R A B) (.cv v) (.cv u) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0037 :=
    @g_syl
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (.cv v))
      (syn_wfo (syn_cun
          (syn_cpprod (syn_cfdpivmap2 R A B) (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid) (syn_cxp (.cv u)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      p0035 p0036
  have p0038 :=
    @g_fdpivmap2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2
      hyp_wppfdpivrangencdlitraw_3
  have p0039 :=
    @g_padontoex u y v f (syn_cfdpivmap2 R A B) dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 p0038
  have p0040 :=
    @g_syl
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wfo (syn_cun
          (syn_cpprod (syn_cfdpivmap2 R A B) (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid) (syn_cxp (.cv u)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv u) (syn_cnnc))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      p0037 p0039
  have p0041 :=
    @g_sucxpinj y z (.cv v) (.cv u) dv_cache_0007 dv_cache_0008 dv_cache_0019
      dv_cache_0009 dv_cache_0020 dv_cache_0021
  have p0042 :=
    @g_sucxpinjex u y z v g dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0016 dv_cache_0017 dv_cache_0026 dv_cache_0018 dv_cache_0027 dv_cache_0021
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @g_a1i
      (syn_wex g (syn_wf1 (.cv g) (syn_cxp (.cv u) (syn_cnnc))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      p0043
  have p0045 :=
    @g_jca
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv u) (syn_cnnc))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      (syn_wex g (syn_wf1 (.cv g) (syn_cxp (.cv u) (syn_cnnc))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      p0040 p0044
  have p0046 := @g_padsetex u y v dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0047 := @g_xnnex u
  have p0048 :=
    @g_pm3_2i
      (.classMem (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cvv))
      (.classMem (syn_cxp (.cv u) (syn_cnnc)) (syn_cvv)) p0046 p0047
  have p0049 :=
    @g_wppcg
      (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cxp (.cv u) (syn_cnnc)) f g h (syn_cvv) (syn_cvv) dv_cache_0028 dv_cache_0028
      dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0050 := Nominal.mp p0048 p0049
  have p0051 :=
    @g_syl5com
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wa (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv u) (syn_cnnc))
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) (syn_wex g
          (syn_wf1 (.cv g) (syn_cxp (.cv u) (syn_cnnc))
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))))
      (syn_wwpp)
      (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
          (syn_cxp (.cv u) (syn_cnnc))))
      p0045 p0050
  have p0052 :=
    @g_taginjex u y v t dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0016
      dv_cache_0017 dv_cache_0018
  have p0053 :=
    @g_a1i
      (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      (syn_wwpp) p0052
  have p0054 :=
    @g_a1i
      (.imp (syn_wwpp) (syn_wex t (syn_wf1 (.cv t) (.cv v)
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))))
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      p0053
  have p0055 :=
    @g_jcad
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wwpp)
      (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
          (syn_cxp (.cv u) (syn_cnnc))))
      (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      p0051 p0054
  have p0056 :=
    @g_f1exco t (.cv v)
      (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cxp (.cv u) (syn_cnnc)) h k dv_cache_0043 dv_cache_0044 dv_cache_0045
      dv_cache_0031 dv_cache_0046 dv_cache_0047 dv_cache_0035 dv_cache_0048 dv_cache_0049
      dv_cache_0050 dv_cache_0051 dv_cache_0052
  have p0057 :=
    @g_a1i
      (.imp (syn_wa (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
                (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
              (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v)
              (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                  (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))))
        (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc)))))
      (syn_wwpp) p0056
  have p0058 :=
    @g_a1i
      (.imp (syn_wwpp) (.imp (syn_wa (syn_wex h (syn_wf1 (.cv h)
                (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                    (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
                (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v)
                (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                    (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))))
          (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc))))))
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      p0057
  have p0059 :=
    @g_mpdd
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wwpp)
      (syn_wa (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
              (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
            (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v)
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))))
      (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc)))) p0055 p0058
  have p0060 := @g_vex v
  have p0062 :=
    @g_nclenc (.cv v) (syn_cxp (.cv u) (syn_cnnc)) k dv_cache_0044 dv_cache_0048 p0060
      p0047
  have p0063 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc))))
        (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc)))))
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      p0062
  have p0064 :=
    @g_sylibrd
      (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)))
      (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc))))
      (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))) p0059
      p0063
  have p0065 :=
    @g_vtoclg
      (.imp (syn_wa (.classEq (.cv u) (syn_cxpk B B))
          (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp)
          (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc))))))
      (.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
          (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp)
          (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))
      u (syn_cxpk B B) (syn_cvv) dv_cache_0053 dv_cache_0054 p0025 p0064
  have p0066 := Nominal.mp p0014 p0065
  have p0067 :=
    @g_vtoclg
      (.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
          (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp)
          (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))
      (.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B))
          (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp)
          (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec)
            (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))
      v (syn_cfdpivrange2 R A B) (syn_cvv) dv_cache_0055 dv_cache_0056 p0013 p0066
  have p0068 := Nominal.mp p0003 p0067
  have p0069 := Nominal.mp p0002 p0068
  exact p0069


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncardsuccshiftedndv (R : Class)
    (hyp_hncardsuccshiftedndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe)
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf
      (syn_wbr (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
        (syn_clec) (syn_chncard
          (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :=
  by
  have dv_cache_0001 :
    Disjoint ((syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))).fv
      (R).fv :=
    by
    exact
      (show Disjoint ((syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))).fv
          (R).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord];
          exact
            (show
              Disjoint (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv)
                ((R).fv)
              from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
                exact
                  (show
                    Disjoint (((syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))).fv) ((R).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
                      exact
                        (show Disjoint (((syn_chnord (syn_cpw1 (syn_c1c)))).fv) ((R).fv)
                          from
                          (by
                            rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord];
                            exact
                              (show Disjoint (((syn_cpw1 (syn_c1c))).fv) ((R).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                                  exact
                                    (show Disjoint (((syn_c1c)).fv) ((R).fv) from
                                      (by
                                        rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
                                        exact
                                          (show Disjoint ((∅ : Finset Var)) ((R).fv) from
                                            (by simp))))))))))))))
  have p0000 :=
    @g_hnwcutmaptc2le (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))) R
      dv_cache_0001 hyp_hncardsuccshiftedndv_1
  have p0001 :=
    (Nominal.classEqRefl (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
  have p0002 :=
    @g_tceq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_tceq (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
      (syn_ctc (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_breq1i
      (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      (syn_ctc (syn_ctc
          (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))
      (syn_clec) p0005
  have p0007 :=
    @g_mpbir
      (syn_wbr (syn_ctc
          (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
        (syn_clec)
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))
        (syn_clec)
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))
      p0000 p0006
  exact p0007

@[expose]
noncomputable def g_kqrelimakndv (A : Class) (B : Class) (_dv_A_B : Disjoint A.fv B.fv) :
    Nominal.NPrf (.classEq (syn_cima (syn_ckqrel A) B) (syn_cimak A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ckqrel A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0004 : Disjoint (A).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (A).fv from (by exact fresh_y_not_A))))))
  have dv_cache_0005 : Disjoint (A).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (A).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (A).fv from (by exact fresh_x_not_A))))))
  have dv_cache_0006 : Disjoint ((Class.cv y)).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv y)).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (y),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (x)];
          exact
            (show Disjoint (({ y } : Finset Var)) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ ({ x } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show y ≠ x from (by exact fresh_y_ne_x))))))))
  have dv_cache_0007 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cima (syn_ckqrel A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cimak A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @g_elima y (.cv x) (syn_ckqrel A) B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv y) (syn_ckqrel A) (.cv x)))
  have p0002 := @g_vex y
  have p0003 := @g_vex x
  have p0004 :=
    @g_kqrelbr A (.cv y) (.cv x) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0002 p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv y) (syn_ckqrel A) (.cv x))
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_ckqrel A))
      (.classMem (syn_copk (.cv y) (.cv x)) A) p0001 p0004
  have p0006 :=
    @g_rexbii (syn_wbr (.cv y) (syn_ckqrel A) (.cv x))
      (.classMem (syn_copk (.cv y) (.cv x)) A) y B p0005
  have p0007 :=
    @g_bitri (.classMem (.cv x) (syn_cima (syn_ckqrel A) B))
      (syn_wrex y B (syn_wbr (.cv y) (syn_ckqrel A) (.cv x)))
      (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)) p0000 p0006
  have p0009 := @g_elimak y A B (.cv x) dv_cache_0007 dv_cache_0003 dv_cache_0001 p0003
  have p0010 :=
    @g_bicomi (.classMem (.cv x) (syn_cimak A B))
      (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)) p0009
  have p0011 :=
    @g_bitri (.classMem (.cv x) (syn_cima (syn_ckqrel A) B))
      (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A))
      (.classMem (.cv x) (syn_cimak A B)) p0007 p0010
  have p0012 :=
    @g_eqriv x (syn_cima (syn_ckqrel A) B) (syn_cimak A B) dv_cache_0008 dv_cache_0009
      p0011
  exact p0012

@[expose]
noncomputable def g_wppqkrelresrangevalndv (A : Class) :
    Nominal.NPrf
      (.classEq (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A))))
        (syn_cqkrel A)) :=
  by
  have dv_cache_0001 : Disjoint ((syn_cwppqkrelkernel)).fv ((syn_cpw1 (syn_cpw1 A))).fv :=
    by
    exact
      (show Disjoint ((syn_cwppqkrelkernel)).fv ((syn_cpw1 (syn_cpw1 A))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
          exact (show Disjoint ((∅ : Finset Var)) (((syn_cpw1 A)).fv) from (by simp))))
  have p0000 := @g_dfima3 (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A))
  have p0001 :=
    @g_eqcomi (syn_cima (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A)))
      (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A))))
      p0000
  have p0002 :=
    @g_kqrelimakndv (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A)) dv_cache_0001
  have p0003 :=
    @g_eqtri
      (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A))))
      (syn_cima (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A)))
      (syn_cimak (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A))) p0001 p0002
  have p0004 := @g_wppqkrelkernelvalndv A
  have p0005 :=
    @g_eqtri
      (syn_crn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 A))))
      (syn_cimak (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A))) (syn_cqkrel A) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_wppqkrelkernelpointbrndv (A : Class) (B : Class) (C : Class)
    (hyp_wppqkrelkernelpointbrndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppqkrelkernelpointbrndv_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_wppqkrelkernelpointbrndv_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (syn_csn A)) (syn_copk B C))
          (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq A (syn_cop B C))) :=
  by
  have p0000 := @g_snex (syn_csn A)
  have p0001 := @g_opkex B C
  have p0002 :=
    @g_pm3_2i (.classMem (syn_csn (syn_csn A)) (syn_cvv))
      (.classMem (syn_copk B C) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_kqrelbrg (syn_cwppqkrelkernel) (syn_csn (syn_csn A)) (syn_copk B C) (syn_cvv)
      (syn_cvv)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cwppqkrelkernel))
  have p0006 :=
    @g_eleq2i (syn_cwppqkrelkernel)
      (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) p0005
  have p0007 :=
    @g_elin (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
      (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
            (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0009 :=
    @g_pm3_2i (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      hyp_wppqkrelkernelpointbrndv_2 hyp_wppqkrelkernelpointbrndv_3
  have p0010 :=
    @g_opkelxpk B C (syn_cvv) (syn_cvv) hyp_wppqkrelkernelpointbrndv_2
      hyp_wppqkrelkernelpointbrndv_3
  have p0011 :=
    @g_mpbir (.classMem (syn_copk B C) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0009 p0010
  have p0012 :=
    @g_pm3_2i (.classMem (syn_csn (syn_csn A)) (syn_cvv))
      (.classMem (syn_copk B C) (syn_cxpk (syn_cvv) (syn_cvv))) p0000 p0011
  have p0015 :=
    @g_opkelxpk (syn_csn (syn_csn A)) (syn_copk B C) (syn_cvv)
      (syn_cxpk (syn_cvv) (syn_cvv)) p0000 p0001
  have p0016 :=
    @g_mpbir
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
        (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wa (.classMem (syn_csn (syn_csn A)) (syn_cvv))
        (.classMem (syn_copk B C) (syn_cxpk (syn_cvv) (syn_cvv))))
      p0012 p0015
  have p0017 :=
    @g_biantrur
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
        (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0016
  have p0018 :=
    @g_bicomi
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
          (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
        (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0017
  have p0019 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
        (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
          (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
        (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0007 p0018
  have p0020 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cwppqkrelkernel))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
        (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0006 p0019
  have p0021 :=
    @g_setconslem3 A B C hyp_wppqkrelkernelpointbrndv_1 hyp_wppqkrelkernelpointbrndv_2
      hyp_wppqkrelkernelpointbrndv_3
  have p0022 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cwppqkrelkernel))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classEq A (syn_cop B C)) p0020 p0021
  have p0023 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (syn_csn A)) (syn_copk B C))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cwppqkrelkernel))
      (.classEq A (syn_cop B C)) p0004 p0022
  exact p0023

@[expose]
noncomputable def g_wppqkrelkernelrangeformndv (A : Class) (D : Class)
    (_hyp_wppqkrelkernelrangeformndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppqkrelkernelrangeformndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
        (.classMem D (syn_cxpk (syn_cvv) (syn_cvv)))) :=
  by
  have p0000 := @g_snex (syn_csn A)
  have p0001 :=
    @g_pm3_2i (.classMem (syn_csn (syn_csn A)) (syn_cvv)) (.classMem D (syn_cvv)) p0000
      hyp_wppqkrelkernelrangeformndv_2
  have p0002 :=
    @g_kqrelbrg (syn_cwppqkrelkernel) (syn_csn (syn_csn A)) D (syn_cvv) (syn_cvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_biimpi
      (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_cwppqkrelkernel)) p0003
  have p0005 := (Nominal.classEqRefl (syn_cwppqkrelkernel))
  have p0006 :=
    @g_eleq2i (syn_cwppqkrelkernel)
      (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_copk (syn_csn (syn_csn A)) D) p0005
  have p0007 :=
    @g_biimpi (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_cwppqkrelkernel))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0006
  have p0008 :=
    @g_syl
      (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_cwppqkrelkernel))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0004 p0007
  have p0009 :=
    @g_elin (syn_copk (syn_csn (syn_csn A)) D)
      (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
            (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0010 :=
    @g_biimpi
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn A)) D)
          (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
        (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0009
  have p0011 :=
    @g_syl
      (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn A)) D)
          (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
        (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0008 p0010
  have p0012 :=
    @g_simpl
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0013 :=
    @g_syl
      (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn A)) D)
          (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
        (.classMem (syn_copk (syn_csn (syn_csn A)) D) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
      p0011 p0012
  have p0015 :=
    @g_opkelxpk (syn_csn (syn_csn A)) D (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)) p0000
      hyp_wppqkrelkernelrangeformndv_2
  have p0016 :=
    @g_biimpi
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wa (.classMem (syn_csn (syn_csn A)) (syn_cvv))
        (.classMem D (syn_cxpk (syn_cvv) (syn_cvv))))
      p0015
  have p0017 :=
    @g_syl
      (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_copk (syn_csn (syn_csn A)) D)
        (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wa (.classMem (syn_csn (syn_csn A)) (syn_cvv))
        (.classMem D (syn_cxpk (syn_cvv) (syn_cvv))))
      p0013 p0016
  have p0018 :=
    @g_simpr (.classMem (syn_csn (syn_csn A)) (syn_cvv))
      (.classMem D (syn_cxpk (syn_cvv) (syn_cvv)))
  have p0019 :=
    @g_syl
      (.classMem (syn_cop (syn_csn (syn_csn A)) D) (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wa (.classMem (syn_csn (syn_csn A)) (syn_cvv))
        (.classMem D (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem D (syn_cxpk (syn_cvv) (syn_cvv))) p0017 p0018
  exact p0019


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppqkrelcanonicalfiberndv (A : Class) (B : Class) (D : Class)
    (hyp_wppqkrelcanonicalfiberndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppqkrelcanonicalfiberndv_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_wppqkrelcanonicalfiberndv_3 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (.classEq D (syn_copk A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 :
    x ∉
      ((Wff.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, fresh_x_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq D (syn_copk A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0008 :
    y ∉
      ((Wff.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, fresh_y_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq D (syn_copk A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @g_opex A B hyp_wppqkrelcanonicalfiberndv_1 hyp_wppqkrelcanonicalfiberndv_2
  have p0001 :=
    @g_wppqkrelkernelrangeformndv (syn_cop A B) D p0000 hyp_wppqkrelcanonicalfiberndv_3
  have p0002 :=
    @g_elxpk x y D (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_biimpi (.classMem D (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      p0002
  have p0004 :=
    @g_syl
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem D (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      p0001 p0003
  have p0005 :=
    @g_nfv
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      x dv_cache_0006
  have p0006 := @g_nfv (.classEq D (syn_copk A B)) x dv_cache_0007
  have p0007 :=
    @g_nfv
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      y dv_cache_0008
  have p0008 := @g_nfv (.classEq D (syn_copk A B)) y dv_cache_0009
  have p0009 :=
    @g_simpr
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
  have p0010 :=
    @g_simpl (.classEq D (syn_copk (.cv x) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq D (syn_copk (.cv x) (.cv y))) p0009 p0010
  have p0012 :=
    @g_simpl
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
  have p0016 :=
    @g_opeq2d
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      D (syn_copk (.cv x) (.cv y)) (syn_csn (syn_csn (syn_cop A B))) p0011
  have p0017 :=
    @g_eleq1d
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
      (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y)))
      (syn_ckqrel (syn_cwppqkrelkernel)) p0016
  have p0018 :=
    @g_mpbid
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y)))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      p0012 p0017
  have p0020 := @g_vex x
  have p0021 := @g_vex y
  have p0022 :=
    @g_wppqkrelkernelpointbrndv (syn_cop A B) (.cv x) (.cv y) p0000 p0020 p0021
  have p0023 :=
    @g_biimpi
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y)))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) p0022
  have p0024 :=
    @g_syl
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk (.cv x) (.cv y)))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) p0018 p0023
  have p0025 := @g_opth A B (.cv x) (.cv y)
  have p0026 :=
    @g_biimpi (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classEq A (.cv x)) (.classEq B (.cv y))) p0025
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classEq A (.cv x)) (.classEq B (.cv y))) p0024 p0026
  have p0028 := @g_opkeq12 A B (.cv x) (.cv y)
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (syn_wa (.classEq A (.cv x)) (.classEq B (.cv y)))
      (.classEq (syn_copk A B) (syn_copk (.cv x) (.cv y))) p0027 p0028
  have p0030 :=
    @g_eqcomd
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (syn_copk A B) (syn_copk (.cv x) (.cv y)) p0029
  have p0031 :=
    @g_eqtrd
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
          (syn_ckqrel (syn_cwppqkrelkernel))) (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      D (syn_copk (.cv x) (.cv y)) (syn_copk A B) p0011 p0030
  have p0032 :=
    @g_ex
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq D (syn_copk A B)) p0031
  have p0033 :=
    @g_exlimd
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (.classEq D (syn_copk A B)) y p0007 p0008 p0032
  have p0034 :=
    @g_exlimd
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (.classEq D (syn_copk A B)) x p0005 p0006 p0033
  have p0035 :=
    @g_mpd
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (syn_wex x (syn_wex y (syn_wa (.classEq D (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      (.classEq D (syn_copk A B)) p0004 p0034
  have p0036 := @g_eqid (syn_cop A B)
  have p0038 :=
    @g_wppqkrelkernelpointbrndv (syn_cop A B) A B p0000 hyp_wppqkrelcanonicalfiberndv_1
      hyp_wppqkrelcanonicalfiberndv_2
  have p0039 :=
    @g_mpbir
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (syn_cop A B) (syn_cop A B)) p0036 p0038
  have p0040 :=
    @g_a1i
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq D (syn_copk A B)) p0039
  have p0041 := @g_id (.classEq D (syn_copk A B))
  have p0042 :=
    @g_opeq2d (.classEq D (syn_copk A B)) D (syn_copk A B)
      (syn_csn (syn_csn (syn_cop A B))) p0041
  have p0043 :=
    @g_eleq1d (.classEq D (syn_copk A B)) (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
      (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B))
      (syn_ckqrel (syn_cwppqkrelkernel)) p0042
  have p0044 :=
    @g_mpbird (.classEq D (syn_copk A B))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (syn_copk A B))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      p0040 p0043
  have p0045 :=
    @g_impbii
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) D)
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq D (syn_copk A B)) p0035 p0044
  exact p0045

@[expose]
noncomputable def g_wppqkrelcanonicaleu (A : Class) (B : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv)
    (hyp_wppqkrelcanonicaleu_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_wppqkrelcanonicaleu_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (.cv d))
          (syn_ckqrel (syn_cwppqkrelkernel)))) :=
  by
  have dv_cache_0001 : d ∉ ((syn_copk A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, dv_A_d, dv_B_d, or_false, not_false_eq_true])
  have p0000 := @g_opkex A B
  have p0001 := @g_eueq1 d (syn_copk A B) dv_cache_0001 p0000
  have p0002 := @g_vex d
  have p0003 :=
    @g_wppqkrelcanonicalfiberndv A B (.cv d) hyp_wppqkrelcanonicaleu_1
      hyp_wppqkrelcanonicaleu_2 p0002
  have p0004 :=
    @g_eubii
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classEq (.cv d) (syn_copk A B)) d p0003
  have p0005 :=
    @g_mpbir
      (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop A B))) (.cv d))
          (syn_ckqrel (syn_cwppqkrelkernel))))
      (syn_weu d (.classEq (.cv d) (syn_copk A B))) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_wppqkrelresfnndv (A : Class) (B : Class)
    (_hyp_wppqkrelresfnndv_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (_hyp_wppqkrelresfnndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_s_ne_u : s ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_s : u ≠ s := Ne.symm fresh_s_ne_u
  have fresh_s_ne_a : s ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_s : a ≠ s := Ne.symm fresh_s_ne_a
  have fresh_s_ne_b : s ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_s : b ≠ s := Ne.symm fresh_s_ne_b
  have fresh_d_ne_u : d ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_d : u ≠ d := Ne.symm fresh_d_ne_u
  have fresh_d_ne_a : d ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_d : a ≠ d := Ne.symm fresh_d_ne_a
  have fresh_d_ne_b : d ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_d : b ≠ d := Ne.symm fresh_d_ne_b
  have fresh_u_ne_a : u ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_u : a ≠ u := Ne.symm fresh_u_ne_a
  have fresh_u_ne_b : u ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_u : b ≠ u := Ne.symm fresh_u_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
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
      ((syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_s, fresh_a_not_A, fresh_a_not_B, fresh_a_ne_u,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    a ∉
      ((syn_weu d
          (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_s,
          fresh_a_ne_d, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    b ∉
      ((syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_s, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_u,
          or_false, not_false_eq_true])
  have dv_cache_0013 :
    b ∉
      ((syn_weu d
          (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_s,
          fresh_b_ne_d, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 : d ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_a, not_false_eq_true])
  have dv_cache_0015 : d ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_b, not_false_eq_true])
  have dv_cache_0016 :
    d ∉
      ((syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
              (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
          (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_s, fresh_d_not_A, fresh_d_not_B, fresh_d_ne_u,
          fresh_d_ne_a, fresh_d_ne_b, or_false, not_false_eq_true])
  have dv_cache_0017 :
    u ∉
      ((syn_weu d
          (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_s,
          fresh_u_ne_d, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    u ∉ ((Wff.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_s, fresh_u_not_A, fresh_u_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0019 : s ∉ ((syn_cpw1 (syn_cpw1 (syn_cxp A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_s_not_A, fresh_s_not_B, or_false, not_false_eq_true])
  have dv_cache_0020 : d ∉ ((syn_cpw1 (syn_cpw1 (syn_cxp A B)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_d_not_A, fresh_d_not_B, or_false, not_false_eq_true])
  have dv_cache_0021 : s ∉ ((syn_ckqrel (syn_cwppqkrelkernel))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0022 : d ∉ ((syn_ckqrel (syn_cwppqkrelkernel))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0023 : s ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show s ≠ d from (by exact fresh_s_ne_d))
  have p0000 := @g_elpw12 u (.cv s) (syn_cxp A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))) p0000
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (.classMem (.cv u) (syn_cxp A B)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0003 :=
    @g_simpr (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (.classMem (.cv u) (syn_cxp A B))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (.classMem (.cv u) (syn_cxp A B)))
      (.classMem (.cv u) (syn_cxp A B)) p0002 p0003
  have p0005 :=
    @g_elxp a b (.cv u) A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0006 :=
    @g_biimpi (.classMem (.cv u) (syn_cxp A B))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0005
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (.classMem (.cv u) (syn_cxp A B))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0004 p0006
  have p0008 :=
    @g_nfv
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      a dv_cache_0010
  have p0009 :=
    @g_nfv
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      a dv_cache_0011
  have p0010 :=
    @g_nfv
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      b dv_cache_0012
  have p0011 :=
    @g_nfv
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      b dv_cache_0013
  have p0012 := @g_vex a
  have p0013 := @g_vex b
  have p0014 :=
    @g_wppqkrelcanonicaleu (.cv a) (.cv b) d dv_cache_0014 dv_cache_0015 p0012 p0013
  have p0015 :=
    @g_a1i
      (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
          (syn_ckqrel (syn_cwppqkrelkernel))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      p0014
  have p0016 :=
    @g_nfv
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      d dv_cache_0016
  have p0017 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0018 :=
    @g_simpr
      (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (.classMem (.cv u) (syn_cxp A B)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))) p0017 p0018
  have p0020 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0021 :=
    @g_simpl (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
      (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv u) (syn_cop (.cv a) (.cv b))) p0020 p0021
  have p0023 := @g_sneq (.cv u) (syn_cop (.cv a) (.cv b))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
      (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))) p0022 p0023
  have p0025 := @g_sneq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b)))
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (syn_csn (.cv u)) (syn_csn (syn_cop (.cv a) (.cv b))))
      (.classEq (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))))
      p0024 p0025
  have p0027 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (syn_csn (syn_csn (.cv u))) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b))))
      p0019 p0026
  have p0028 :=
    @g_opeq1d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d) p0027
  have p0029 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_cop (.cv s) (.cv d))
      (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
      (syn_ckqrel (syn_cwppqkrelkernel)) p0028
  have p0030 :=
    @g_eubid
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))
      (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
        (syn_ckqrel (syn_cwppqkrelkernel)))
      d p0016 p0029
  have p0031 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
            (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
        (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      (syn_weu d (.classMem (syn_cop (syn_csn (syn_csn (syn_cop (.cv a) (.cv b)))) (.cv d))
          (syn_ckqrel (syn_cwppqkrelkernel))))
      p0015 p0030
  have p0032 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      p0031
  have p0033 :=
    @g_exlimd
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      b p0010 p0011 p0032
  have p0034 :=
    @g_exlimd
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
          (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      a p0008 p0009 p0033
  have p0035 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
          (.classMem (.cv u) (syn_cxp A B))) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv u) (syn_cop (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      p0007 p0034
  have p0036 :=
    @g_ex
      (syn_wa (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (.classMem (.cv u) (syn_cxp A B)))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      p0035
  have p0037 :=
    @g_rexlimdva (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (.classEq (.cv s) (syn_csn (syn_csn (.cv u))))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      u (syn_cxp A B) dv_cache_0017 dv_cache_0018 p0036
  have p0038 :=
    @g_mpd (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wrex u (syn_cxp A B) (.classEq (.cv s) (syn_csn (syn_csn (.cv u)))))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      p0001 p0037
  have p0039 :=
    (Nominal.biimpRefl (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)))
  have p0040 :=
    @g_eubii (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))
      (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))) d p0039
  have p0041 :=
    @g_a1i
      (syn_wb (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)))
        (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel)))))
      (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B)))) p0040
  have p0042 :=
    @g_mpbird (.classMem (.cv s) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d)))
      (syn_weu d (.classMem (syn_cop (.cv s) (.cv d)) (syn_ckqrel (syn_cwppqkrelkernel))))
      p0038 p0041
  have p0043 :=
    @g_rgen (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))) s
      (syn_cpw1 (syn_cpw1 (syn_cxp A B))) p0042
  have p0044 :=
    @g_fnres s d (syn_cpw1 (syn_cpw1 (syn_cxp A B))) (syn_ckqrel (syn_cwppqkrelkernel))
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0045 :=
    @g_mpbir
      (syn_wfn (syn_cres (syn_ckqrel (syn_cwppqkrelkernel)) (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
        (syn_cpw1 (syn_cpw1 (syn_cxp A B))))
      (syn_wral s (syn_cpw1 (syn_cpw1 (syn_cxp A B)))
        (syn_weu d (syn_wbr (.cv s) (syn_ckqrel (syn_cwppqkrelkernel)) (.cv d))))
      p0043 p0044
  exact p0045


end NFChoice.DirectNominalPrf.WPPReplay

end
