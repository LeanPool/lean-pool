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

/-- Checked nominal proof certificate identified upstream as `g_wppfdpivrangencdlitraw`. -/
@[expose]
noncomputable def gWppfdpivrangencdlitraw (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_wppfdpivrangencdlitraw_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_wppfdpivrangencdlitraw_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppfdpivrangencdlitraw_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWbr (synCnc (synCfdpivrange2 R A B)) (synClec)
          (synCnc (synCxp (synCxpk B B) (synCnnc))))) :=
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
  have dv_cache_0004 : Disjoint ((synCfdpivmap2 R A B)).fv ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((synCfdpivmap2 R A B)).fv ((Class.cv v)).fv from (by
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
  have dv_cache_0005 : Disjoint ((synCfdpivmap2 R A B)).fv ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint ((synCfdpivmap2 R A B)).fv ((Class.cv u)).fv from (by
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
  have dv_cache_0006 : y ∉ ((synCfdpivmap2 R A B)).fv :=
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
  have dv_cache_0010 : f ∉ ((synCfdpivmap2 R A B)).fv :=
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
  have dv_cache_0011 : v ∉ ((synCfdpivmap2 R A B)).fv :=
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
  have dv_cache_0012 : u ∉ ((synCfdpivmap2 R A B)).fv :=
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
      ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv
      ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (show Disjoint ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv ((synCvv)).fv
        from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact
            (show
              Disjoint
                ((((synCxp (.cv v) (synCsn (synC0c)))).fv) ∪
                  (((synCxp (.cv u)
                      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))).fv))
                ((∅ : Finset Var))
              from
              (Finset.disjoint_union_left.mpr
                ⟨(show
                    Disjoint (((synCxp (.cv v) (synCsn (synC0c)))).fv)
                      ((∅ : Finset Var))
                    from (by simp)),
                  (show
                    Disjoint
                      (((synCxp (.cv u)
                          (synCrab y (synCnnc)
                            (.neg (.classEq (.cv y) (synC0c)))))).fv)
                      ((∅ : Finset Var))
                    from (by simp))⟩))))
  have dv_cache_0029 :
    f ∉
      ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv :=
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
      ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv :=
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
      ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv :=
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
  have dv_cache_0032 : Disjoint ((synCxp (.cv u) (synCnnc))).fv ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (show Disjoint ((synCxp (.cv u) (synCnnc))).fv ((synCvv)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact
            (show Disjoint ((((Class.cv u)).fv) ∪ (((synCnnc)).fv)) ((∅ : Finset Var))
              from
              (Finset.disjoint_union_left.mpr
                ⟨(show Disjoint (((Class.cv u)).fv) ((∅ : Finset Var)) from (by simp)),
                  (show Disjoint (((synCnnc)).fv) ((∅ : Finset Var)) from (by simp))⟩))))
  have dv_cache_0033 : f ∉ ((synCxp (.cv u) (synCnnc))).fv :=
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
  have dv_cache_0034 : g ∉ ((synCxp (.cv u) (synCnnc))).fv :=
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
  have dv_cache_0035 : h ∉ ((synCxp (.cv u) (synCnnc))).fv :=
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
  have dv_cache_0036 : Disjoint ((synCvv)).fv ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (show Disjoint ((synCvv)).fv ((synCvv)).fv from (by
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
      ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv :=
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
      ((synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))).fv :=
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
  have dv_cache_0048 : k ∉ ((synCxp (.cv u) (synCnnc))).fv :=
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
  have dv_cache_0049 : t ∉ ((synCxp (.cv u) (synCnnc))).fv :=
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
  have dv_cache_0053 : u ∉ ((synCxpk B B)).fv :=
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
      ((Wff.imp (synWa (.classEq (synCxpk B B) (synCxpk B B))
            (.classEq (.cv v) (synCfdpivrange2 R A B))) (.imp (synWwpp)
            (synWbr (synCnc (.cv v)) (synClec)
              (synCnc (synCxp (synCxpk B B) (synCnnc))))))).fv :=
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
  have dv_cache_0055 : v ∉ ((synCfdpivrange2 R A B)).fv :=
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
      ((Wff.imp (synWa (.classEq (synCxpk B B) (synCxpk B B))
            (.classEq (synCfdpivrange2 R A B) (synCfdpivrange2 R A B))) (.imp (synWwpp)
            (synWbr (synCnc (synCfdpivrange2 R A B)) (synClec)
              (synCnc (synCxp (synCxpk B B) (synCnnc))))))).fv :=
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
  have p0000 := @gEqid (synCxpk B B)
  have p0001 := @gEqid (synCfdpivrange2 R A B)
  have p0002 :=
    @gPm32i (.classEq (synCxpk B B) (synCxpk B B))
      (.classEq (synCfdpivrange2 R A B) (synCfdpivrange2 R A B)) p0000 p0001
  have p0003 :=
    @gFdpivrange2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2
      hyp_wppfdpivrangencdlitraw_3
  have p0004 :=
    @gBiidd (.classEq (.cv v) (synCfdpivrange2 R A B))
      (.classEq (synCxpk B B) (synCxpk B B))
  have p0005 := @gId (.classEq (.cv v) (synCfdpivrange2 R A B))
  have p0006 :=
    @gEqeq1d (.classEq (.cv v) (synCfdpivrange2 R A B)) (.cv v) (synCfdpivrange2 R A B)
      (synCfdpivrange2 R A B) p0005
  have p0007 :=
    @gAnbi12d (.classEq (.cv v) (synCfdpivrange2 R A B))
      (.classEq (synCxpk B B) (synCxpk B B)) (.classEq (synCxpk B B) (synCxpk B B))
      (.classEq (.cv v) (synCfdpivrange2 R A B))
      (.classEq (synCfdpivrange2 R A B) (synCfdpivrange2 R A B)) p0004 p0006
  have p0008 := @gBiidd (.classEq (.cv v) (synCfdpivrange2 R A B)) (synWwpp)
  have p0010 :=
    @gNceqd (.classEq (.cv v) (synCfdpivrange2 R A B)) (.cv v) (synCfdpivrange2 R A B)
      p0005
  have p0011 :=
    @gBreq1d (.classEq (.cv v) (synCfdpivrange2 R A B)) (synCnc (.cv v))
      (synCnc (synCfdpivrange2 R A B)) (synCnc (synCxp (synCxpk B B) (synCnnc)))
      (synClec) p0010
  have p0012 :=
    @gImbi12d (.classEq (.cv v) (synCfdpivrange2 R A B)) (synWwpp) (synWwpp)
      (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (synCxpk B B) (synCnnc))))
      (synWbr (synCnc (synCfdpivrange2 R A B)) (synClec)
        (synCnc (synCxp (synCxpk B B) (synCnnc))))
      p0008 p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv v) (synCfdpivrange2 R A B))
      (synWa (.classEq (synCxpk B B) (synCxpk B B))
        (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWa (.classEq (synCxpk B B) (synCxpk B B))
        (.classEq (synCfdpivrange2 R A B) (synCfdpivrange2 R A B)))
      (.imp (synWwpp) (synWbr (synCnc (.cv v)) (synClec)
          (synCnc (synCxp (synCxpk B B) (synCnnc)))))
      (.imp (synWwpp) (synWbr (synCnc (synCfdpivrange2 R A B)) (synClec)
          (synCnc (synCxp (synCxpk B B) (synCnnc)))))
      p0007 p0012
  have p0014 := @gXpkex B B hyp_wppfdpivrangencdlitraw_3 hyp_wppfdpivrangencdlitraw_3
  have p0015 := @gId (.classEq (.cv u) (synCxpk B B))
  have p0016 :=
    @gEqeq1d (.classEq (.cv u) (synCxpk B B)) (.cv u) (synCxpk B B) (synCxpk B B)
      p0015
  have p0017 :=
    @gBiidd (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B))
  have p0018 :=
    @gAnbi12d (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv u) (synCxpk B B))
      (.classEq (synCxpk B B) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B))
      (.classEq (.cv v) (synCfdpivrange2 R A B)) p0016 p0017
  have p0019 := @gBiidd (.classEq (.cv u) (synCxpk B B)) (synWwpp)
  have p0021 :=
    @gXpeq1d (.classEq (.cv u) (synCxpk B B)) (.cv u) (synCxpk B B) (synCnnc) p0015
  have p0022 :=
    @gNceqd (.classEq (.cv u) (synCxpk B B)) (synCxp (.cv u) (synCnnc))
      (synCxp (synCxpk B B) (synCnnc)) p0021
  have p0023 :=
    @gBreq2d (.classEq (.cv u) (synCxpk B B)) (synCnc (synCxp (.cv u) (synCnnc)))
      (synCnc (synCxp (synCxpk B B) (synCnnc))) (synCnc (.cv v)) (synClec) p0022
  have p0024 :=
    @gImbi12d (.classEq (.cv u) (synCxpk B B)) (synWwpp) (synWwpp)
      (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (.cv u) (synCnnc))))
      (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (synCxpk B B) (synCnnc))))
      p0019 p0023
  have p0025 :=
    @gImbi12d (.classEq (.cv u) (synCxpk B B))
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWa (.classEq (synCxpk B B) (synCxpk B B))
        (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (.imp (synWwpp)
        (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (.cv u) (synCnnc)))))
      (.imp (synWwpp) (synWbr (synCnc (.cv v)) (synClec)
          (synCnc (synCxp (synCxpk B B) (synCnnc)))))
      p0018 p0024
  have p0026 :=
    @gFdpivmap2onto A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2
      hyp_wppfdpivrangencdlitraw_3
  have p0027 :=
    @gA1i (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCfdpivrange2 R A B))
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      p0026
  have p0028 :=
    @gSimpl (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B))
  have p0029 :=
    @gFoeq2 (.cv u) (synCxpk B B) (synCfdpivrange2 R A B) (synCfdpivmap2 R A B)
  have p0030 :=
    @gSyl
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (.classEq (.cv u) (synCxpk B B))
      (synWb (synWfo (synCfdpivmap2 R A B) (.cv u) (synCfdpivrange2 R A B))
        (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCfdpivrange2 R A B)))
      p0028 p0029
  have p0031 :=
    @gMpbird
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWfo (synCfdpivmap2 R A B) (.cv u) (synCfdpivrange2 R A B))
      (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCfdpivrange2 R A B)) p0027 p0030
  have p0032 :=
    @gSimpr (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B))
  have p0033 := @gFoeq3 (.cv v) (synCfdpivrange2 R A B) (.cv u) (synCfdpivmap2 R A B)
  have p0034 :=
    @gSyl
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (.classEq (.cv v) (synCfdpivrange2 R A B))
      (synWb (synWfo (synCfdpivmap2 R A B) (.cv u) (.cv v))
        (synWfo (synCfdpivmap2 R A B) (.cv u) (synCfdpivrange2 R A B)))
      p0032 p0033
  have p0035 :=
    @gMpbird
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWfo (synCfdpivmap2 R A B) (.cv u) (.cv v))
      (synWfo (synCfdpivmap2 R A B) (.cv u) (synCfdpivrange2 R A B)) p0031 p0034
  have p0036 :=
    @gWpppadonto y (synCfdpivmap2 R A B) (.cv v) (.cv u) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0037 :=
    @gSyl
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWfo (synCfdpivmap2 R A B) (.cv u) (.cv v))
      (synWfo (synCun
          (synCpprod (synCfdpivmap2 R A B) (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid) (synCxp (.cv u)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synCxp (.cv u) (synCnnc)) (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      p0035 p0036
  have p0038 :=
    @gFdpivmap2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2
      hyp_wppfdpivrangencdlitraw_3
  have p0039 :=
    @gPadontoex u y v f (synCfdpivmap2 R A B) dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 p0038
  have p0040 :=
    @gSyl
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWfo (synCun
          (synCpprod (synCfdpivmap2 R A B) (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid) (synCxp (.cv u)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synCxp (.cv u) (synCnnc)) (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (synWex f (synWfo (.cv f) (synCxp (.cv u) (synCnnc))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      p0037 p0039
  have p0041 :=
    @gSucxpinj y z (.cv v) (.cv u) dv_cache_0007 dv_cache_0008 dv_cache_0019
      dv_cache_0009 dv_cache_0020 dv_cache_0021
  have p0042 :=
    @gSucxpinjex u y z v g dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      dv_cache_0016 dv_cache_0017 dv_cache_0026 dv_cache_0018 dv_cache_0027 dv_cache_0021
  have p0043 := Nominal.mp p0041 p0042
  have p0044 :=
    @gA1i
      (synWex g (synWf1 (.cv g) (synCxp (.cv u) (synCnnc))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      p0043
  have p0045 :=
    @gJca
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWex f (synWfo (.cv f) (synCxp (.cv u) (synCnnc))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      (synWex g (synWf1 (.cv g) (synCxp (.cv u) (synCnnc))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      p0040 p0044
  have p0046 := @gPadsetex u y v dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0047 := @gXnnex u
  have p0048 :=
    @gPm32i
      (.classMem (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCvv))
      (.classMem (synCxp (.cv u) (synCnnc)) (synCvv)) p0046 p0047
  have p0049 :=
    @gWppcg
      (synCun (synCxp (.cv v) (synCsn (synC0c)))
        (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCxp (.cv u) (synCnnc)) f g h (synCvv) (synCvv) dv_cache_0028 dv_cache_0028
      dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0050 := Nominal.mp p0048 p0049
  have p0051 :=
    @gSyl5com
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWa (synWex f (synWfo (.cv f) (synCxp (.cv u) (synCnnc))
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))) (synWex g
          (synWf1 (.cv g) (synCxp (.cv u) (synCnnc))
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))))
      (synWwpp)
      (synWex h (synWf1 (.cv h) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
          (synCxp (.cv u) (synCnnc))))
      p0045 p0050
  have p0052 :=
    @gTaginjex u y v t dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0016
      dv_cache_0017 dv_cache_0018
  have p0053 :=
    @gA1i
      (synWex t (synWf1 (.cv t) (.cv v) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      (synWwpp) p0052
  have p0054 :=
    @gA1i
      (.imp (synWwpp) (synWex t (synWf1 (.cv t) (.cv v)
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))))
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      p0053
  have p0055 :=
    @gJcad
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWwpp)
      (synWex h (synWf1 (.cv h) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
          (synCxp (.cv u) (synCnnc))))
      (synWex t (synWf1 (.cv t) (.cv v) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      p0051 p0054
  have p0056 :=
    @gF1exco t (.cv v)
      (synCun (synCxp (.cv v) (synCsn (synC0c)))
        (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCxp (.cv u) (synCnnc)) h k dv_cache_0043 dv_cache_0044 dv_cache_0045
      dv_cache_0031 dv_cache_0046 dv_cache_0047 dv_cache_0035 dv_cache_0048 dv_cache_0049
      dv_cache_0050 dv_cache_0051 dv_cache_0052
  have p0057 :=
    @gA1i
      (.imp (synWa (synWex h (synWf1 (.cv h) (synCun (synCxp (.cv v) (synCsn (synC0c)))
                (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
              (synCxp (.cv u) (synCnnc)))) (synWex t (synWf1 (.cv t) (.cv v)
              (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                  (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))))
        (synWex k (synWf1 (.cv k) (.cv v) (synCxp (.cv u) (synCnnc)))))
      (synWwpp) p0056
  have p0058 :=
    @gA1i
      (.imp (synWwpp) (.imp (synWa (synWex h (synWf1 (.cv h)
                (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                    (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
                (synCxp (.cv u) (synCnnc)))) (synWex t (synWf1 (.cv t) (.cv v)
                (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                    (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))))
          (synWex k (synWf1 (.cv k) (.cv v) (synCxp (.cv u) (synCnnc))))))
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      p0057
  have p0059 :=
    @gMpdd
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWwpp)
      (synWa (synWex h (synWf1 (.cv h) (synCun (synCxp (.cv v) (synCsn (synC0c)))
              (synCxp (.cv u) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
            (synCxp (.cv u) (synCnnc)))) (synWex t (synWf1 (.cv t) (.cv v)
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv u)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))))
      (synWex k (synWf1 (.cv k) (.cv v) (synCxp (.cv u) (synCnnc)))) p0055 p0058
  have p0060 := @gVex v
  have p0062 :=
    @gNclenc (.cv v) (synCxp (.cv u) (synCnnc)) k dv_cache_0044 dv_cache_0048 p0060
      p0047
  have p0063 :=
    @gA1i
      (synWb (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (.cv u) (synCnnc))))
        (synWex k (synWf1 (.cv k) (.cv v) (synCxp (.cv u) (synCnnc)))))
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      p0062
  have p0064 :=
    @gSylibrd
      (synWa (.classEq (.cv u) (synCxpk B B)) (.classEq (.cv v) (synCfdpivrange2 R A B)))
      (synWwpp) (synWex k (synWf1 (.cv k) (.cv v) (synCxp (.cv u) (synCnnc))))
      (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (.cv u) (synCnnc)))) p0059
      p0063
  have p0065 :=
    @gVtoclg
      (.imp (synWa (.classEq (.cv u) (synCxpk B B))
          (.classEq (.cv v) (synCfdpivrange2 R A B))) (.imp (synWwpp)
          (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (.cv u) (synCnnc))))))
      (.imp (synWa (.classEq (synCxpk B B) (synCxpk B B))
          (.classEq (.cv v) (synCfdpivrange2 R A B))) (.imp (synWwpp)
          (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (synCxpk B B) (synCnnc))))))
      u (synCxpk B B) (synCvv) dv_cache_0053 dv_cache_0054 p0025 p0064
  have p0066 := Nominal.mp p0014 p0065
  have p0067 :=
    @gVtoclg
      (.imp (synWa (.classEq (synCxpk B B) (synCxpk B B))
          (.classEq (.cv v) (synCfdpivrange2 R A B))) (.imp (synWwpp)
          (synWbr (synCnc (.cv v)) (synClec) (synCnc (synCxp (synCxpk B B) (synCnnc))))))
      (.imp (synWa (.classEq (synCxpk B B) (synCxpk B B))
          (.classEq (synCfdpivrange2 R A B) (synCfdpivrange2 R A B))) (.imp (synWwpp)
          (synWbr (synCnc (synCfdpivrange2 R A B)) (synClec)
            (synCnc (synCxp (synCxpk B B) (synCnnc))))))
      v (synCfdpivrange2 R A B) (synCvv) dv_cache_0055 dv_cache_0056 p0013 p0066
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

/-- Checked nominal proof certificate identified upstream as `g_hncardsuccshiftedndv`. -/
@[expose]
noncomputable def gHncardsuccshiftedndv (R : Class)
    (hyp_hncardsuccshiftedndv_1 : Nominal.NPrf (synWbr R (synCwe)
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :
    Nominal.NPrf
      (synWbr (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
        (synClec) (synChncard
          (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))) :=
  by
  have dv_cache_0001 :
    Disjoint ((synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))).fv
      (R).fv :=
    by
    exact
      (show Disjoint ((synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))).fv
          (R).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord];
          exact
            (show
              Disjoint (((synCpw (synCpw (synChnord (synCpw1 (synC1c)))))).fv)
                ((R).fv)
              from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
                exact
                  (show
                    Disjoint (((synCpw (synChnord (synCpw1 (synC1c))))).fv) ((R).fv)
                    from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
                      exact
                        (show Disjoint (((synChnord (synCpw1 (synC1c)))).fv) ((R).fv)
                          from
                          (by
                            rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord];
                            exact
                              (show Disjoint (((synCpw1 (synC1c))).fv) ((R).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
                                  exact
                                    (show Disjoint (((synC1c)).fv) ((R).fv) from
                                      (by
                                        rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
                                        exact
                                          (show Disjoint ((∅ : Finset Var)) ((R).fv) from
                                            (by simp))))))))))))))
  have p0000 :=
    @gHnwcutmaptc2le (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))) R
      dv_cache_0001 hyp_hncardsuccshiftedndv_1
  have p0001 :=
    (Nominal.classEqRefl (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
  have p0002 :=
    @gTceq (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))
      (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gTceq (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
      (synCtc (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gBreq1i
      (synCtc (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      (synCtc (synCtc
          (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))
      (synChncard (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))
      (synClec) p0005
  have p0007 :=
    @gMpbir
      (synWbr (synCtc
          (synCtc (synChncard (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
        (synClec)
        (synChncard (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      (synWbr (synCtc (synCtc
            (synCnc (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c)))))))))
        (synClec)
        (synChncard (synChnord (synCpw (synCpw (synChnord (synCpw1 (synC1c))))))))
      p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_kqrelimakndv`. -/
@[expose]
noncomputable def gKqrelimakndv (A : Class) (B : Class) (_dv_A_B : Disjoint A.fv B.fv) :
    Nominal.NPrf (.classEq (synCima (synCkqrel A) B) (synCimak A B)) :=
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
  have dv_cache_0002 : y ∉ ((synCkqrel A)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCima (synCkqrel A) B)).fv :=
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
  have dv_cache_0009 : x ∉ ((synCimak A B)).fv :=
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
    @gElima y (.cv x) (synCkqrel A) B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (synWbr (.cv y) (synCkqrel A) (.cv x)))
  have p0002 := @gVex y
  have p0003 := @gVex x
  have p0004 :=
    @gKqrelbr A (.cv y) (.cv x) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0002 p0003
  have p0005 :=
    @gBitri (synWbr (.cv y) (synCkqrel A) (.cv x))
      (.classMem (synCop (.cv y) (.cv x)) (synCkqrel A))
      (.classMem (synCopk (.cv y) (.cv x)) A) p0001 p0004
  have p0006 :=
    @gRexbii (synWbr (.cv y) (synCkqrel A) (.cv x))
      (.classMem (synCopk (.cv y) (.cv x)) A) y B p0005
  have p0007 :=
    @gBitri (.classMem (.cv x) (synCima (synCkqrel A) B))
      (synWrex y B (synWbr (.cv y) (synCkqrel A) (.cv x)))
      (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A)) p0000 p0006
  have p0009 := @gElimak y A B (.cv x) dv_cache_0007 dv_cache_0003 dv_cache_0001 p0003
  have p0010 :=
    @gBicomi (.classMem (.cv x) (synCimak A B))
      (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A)) p0009
  have p0011 :=
    @gBitri (.classMem (.cv x) (synCima (synCkqrel A) B))
      (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A))
      (.classMem (.cv x) (synCimak A B)) p0007 p0010
  have p0012 :=
    @gEqriv x (synCima (synCkqrel A) B) (synCimak A B) dv_cache_0008 dv_cache_0009
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelresrangevalndv`. -/
@[expose]
noncomputable def gWppqkrelresrangevalndv (A : Class) :
    Nominal.NPrf
      (.classEq (synCrn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A))))
        (synCqkrel A)) :=
  by
  have dv_cache_0001 : Disjoint ((synCwppqkrelkernel)).fv ((synCpw1 (synCpw1 A))).fv :=
    by
    exact
      (show Disjoint ((synCwppqkrelkernel)).fv ((synCpw1 (synCpw1 A))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppqkrelkernel,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
          exact (show Disjoint ((∅ : Finset Var)) (((synCpw1 A)).fv) from (by simp))))
  have p0000 := @gDfima3 (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A))
  have p0001 :=
    @gEqcomi (synCima (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A)))
      (synCrn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A))))
      p0000
  have p0002 :=
    @gKqrelimakndv (synCwppqkrelkernel) (synCpw1 (synCpw1 A)) dv_cache_0001
  have p0003 :=
    @gEqtri
      (synCrn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A))))
      (synCima (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A)))
      (synCimak (synCwppqkrelkernel) (synCpw1 (synCpw1 A))) p0001 p0002
  have p0004 := @gWppqkrelkernelvalndv A
  have p0005 :=
    @gEqtri
      (synCrn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 A))))
      (synCimak (synCwppqkrelkernel) (synCpw1 (synCpw1 A))) (synCqkrel A) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelkernelpointbrndv`. -/
@[expose]
noncomputable def gWppqkrelkernelpointbrndv (A : Class) (B : Class) (C : Class)
    (hyp_wppqkrelkernelpointbrndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppqkrelkernelpointbrndv_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_wppqkrelkernelpointbrndv_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (synCsn A)) (synCopk B C))
          (synCkqrel (synCwppqkrelkernel))) (.classEq A (synCop B C))) :=
  by
  have p0000 := @gSnex (synCsn A)
  have p0001 := @gOpkex B C
  have p0002 :=
    @gPm32i (.classMem (synCsn (synCsn A)) (synCvv))
      (.classMem (synCopk B C) (synCvv)) p0000 p0001
  have p0003 :=
    @gKqrelbrg (synCwppqkrelkernel) (synCsn (synCsn A)) (synCopk B C) (synCvv)
      (synCvv)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCwppqkrelkernel))
  have p0006 :=
    @gEleq2i (synCwppqkrelkernel)
      (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCopk (synCsn (synCsn A)) (synCopk B C)) p0005
  have p0007 :=
    @gElin (synCopk (synCsn (synCsn A)) (synCopk B C))
      (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
      (synCcompl (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
            (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                  (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0009 :=
    @gPm32i (.classMem B (synCvv)) (.classMem C (synCvv))
      hyp_wppqkrelkernelpointbrndv_2 hyp_wppqkrelkernelpointbrndv_3
  have p0010 :=
    @gOpkelxpk B C (synCvv) (synCvv) hyp_wppqkrelkernelpointbrndv_2
      hyp_wppqkrelkernelpointbrndv_3
  have p0011 :=
    @gMpbir (.classMem (synCopk B C) (synCxpk (synCvv) (synCvv)))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) p0009 p0010
  have p0012 :=
    @gPm32i (.classMem (synCsn (synCsn A)) (synCvv))
      (.classMem (synCopk B C) (synCxpk (synCvv) (synCvv))) p0000 p0011
  have p0015 :=
    @gOpkelxpk (synCsn (synCsn A)) (synCopk B C) (synCvv)
      (synCxpk (synCvv) (synCvv)) p0000 p0001
  have p0016 :=
    @gMpbir
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C))
        (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
      (synWa (.classMem (synCsn (synCsn A)) (synCvv))
        (.classMem (synCopk B C) (synCxpk (synCvv) (synCvv))))
      p0012 p0015
  have p0017 :=
    @gBiantrur
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C))
        (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0016
  have p0018 :=
    @gBicomi
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C))
          (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
        (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0017
  have p0019 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C))
        (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C))
          (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
        (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0007 p0018
  have p0020 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCwppqkrelkernel))
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C))
        (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0006 p0019
  have p0021 :=
    @gSetconslem3 A B C hyp_wppqkrelkernelpointbrndv_1 hyp_wppqkrelkernelpointbrndv_2
      hyp_wppqkrelkernelpointbrndv_3
  have p0022 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCwppqkrelkernel))
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (.classEq A (synCop B C)) p0020 p0021
  have p0023 :=
    @gBitri
      (.classMem (synCop (synCsn (synCsn A)) (synCopk B C))
        (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCwppqkrelkernel))
      (.classEq A (synCop B C)) p0004 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelkernelrangeformndv`. -/
@[expose]
noncomputable def gWppqkrelkernelrangeformndv (A : Class) (D : Class)
    (_hyp_wppqkrelkernelrangeformndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppqkrelkernelrangeformndv_2 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
        (.classMem D (synCxpk (synCvv) (synCvv)))) :=
  by
  have p0000 := @gSnex (synCsn A)
  have p0001 :=
    @gPm32i (.classMem (synCsn (synCsn A)) (synCvv)) (.classMem D (synCvv)) p0000
      hyp_wppqkrelkernelrangeformndv_2
  have p0002 :=
    @gKqrelbrg (synCwppqkrelkernel) (synCsn (synCsn A)) D (synCvv) (synCvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gBiimpi
      (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCopk (synCsn (synCsn A)) D) (synCwppqkrelkernel)) p0003
  have p0005 := (Nominal.classEqRefl (synCwppqkrelkernel))
  have p0006 :=
    @gEleq2i (synCwppqkrelkernel)
      (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCopk (synCsn (synCsn A)) D) p0005
  have p0007 :=
    @gBiimpi (.classMem (synCopk (synCsn (synCsn A)) D) (synCwppqkrelkernel))
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0006
  have p0008 :=
    @gSyl
      (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCopk (synCsn (synCsn A)) D) (synCwppqkrelkernel))
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0004 p0007
  have p0009 :=
    @gElin (synCopk (synCsn (synCsn A)) D)
      (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
      (synCcompl (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
            (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                  (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
  have p0010 :=
    @gBiimpi
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCopk (synCsn (synCsn A)) D)
          (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
        (.classMem (synCopk (synCsn (synCsn A)) D) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0009
  have p0011 :=
    @gSyl
      (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCopk (synCsn (synCsn A)) D)
          (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
        (.classMem (synCopk (synCsn (synCsn A)) D) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0008 p0010
  have p0012 :=
    @gSimpl
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCopk (synCsn (synCsn A)) D) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  have p0013 :=
    @gSyl
      (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
      (synWa (.classMem (synCopk (synCsn (synCsn A)) D)
          (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
        (.classMem (synCopk (synCsn (synCsn A)) D) (synCcompl (synCimak
              (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                    (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
      p0011 p0012
  have p0015 :=
    @gOpkelxpk (synCsn (synCsn A)) D (synCvv) (synCxpk (synCvv) (synCvv)) p0000
      hyp_wppqkrelkernelrangeformndv_2
  have p0016 :=
    @gBiimpi
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
      (synWa (.classMem (synCsn (synCsn A)) (synCvv))
        (.classMem D (synCxpk (synCvv) (synCvv))))
      p0015
  have p0017 :=
    @gSyl
      (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCopk (synCsn (synCsn A)) D)
        (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))))
      (synWa (.classMem (synCsn (synCsn A)) (synCvv))
        (.classMem D (synCxpk (synCvv) (synCvv))))
      p0013 p0016
  have p0018 :=
    @gSimpr (.classMem (synCsn (synCsn A)) (synCvv))
      (.classMem D (synCxpk (synCvv) (synCvv)))
  have p0019 :=
    @gSyl
      (.classMem (synCop (synCsn (synCsn A)) D) (synCkqrel (synCwppqkrelkernel)))
      (synWa (.classMem (synCsn (synCsn A)) (synCvv))
        (.classMem D (synCxpk (synCvv) (synCvv))))
      (.classMem D (synCxpk (synCvv) (synCvv))) p0017 p0018
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

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelcanonicalfiberndv`. -/
@[expose]
noncomputable def gWppqkrelcanonicalfiberndv (A : Class) (B : Class) (D : Class)
    (hyp_wppqkrelcanonicalfiberndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppqkrelcanonicalfiberndv_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_wppqkrelcanonicalfiberndv_3 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (.classEq D (synCopk A B))) :=
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
  have dv_cache_0003 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCvv)).fv :=
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
      ((Wff.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel)))).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classEq D (synCopk A B))).fv :=
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
      ((Wff.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel)))).fv :=
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
  have dv_cache_0009 : y ∉ ((Wff.classEq D (synCopk A B))).fv :=
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
    @gOpex A B hyp_wppqkrelcanonicalfiberndv_1 hyp_wppqkrelcanonicalfiberndv_2
  have p0001 :=
    @gWppqkrelkernelrangeformndv (synCop A B) D p0000 hyp_wppqkrelcanonicalfiberndv_3
  have p0002 :=
    @gElxpk x y D (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0003 :=
    @gBiimpi (.classMem D (synCxpk (synCvv) (synCvv)))
      (synWex x (synWex y (synWa (.classEq D (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      p0002
  have p0004 :=
    @gSyl
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (.classMem D (synCxpk (synCvv) (synCvv)))
      (synWex x (synWex y (synWa (.classEq D (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      p0001 p0003
  have p0005 :=
    @gNfv
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      x dv_cache_0006
  have p0006 := @gNfv (.classEq D (synCopk A B)) x dv_cache_0007
  have p0007 :=
    @gNfv
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      y dv_cache_0008
  have p0008 := @gNfv (.classEq D (synCopk A B)) y dv_cache_0009
  have p0009 :=
    @gSimpr
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (synWa (.classEq D (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
  have p0010 :=
    @gSimpl (.classEq D (synCopk (.cv x) (.cv y)))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
  have p0011 :=
    @gSyl
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (synWa (.classEq D (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq D (synCopk (.cv x) (.cv y))) p0009 p0010
  have p0012 :=
    @gSimpl
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (synWa (.classEq D (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
  have p0016 :=
    @gOpeq2d
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      D (synCopk (.cv x) (.cv y)) (synCsn (synCsn (synCop A B))) p0011
  have p0017 :=
    @gEleq1d
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (synCop (synCsn (synCsn (synCop A B))) D)
      (synCop (synCsn (synCsn (synCop A B))) (synCopk (.cv x) (.cv y)))
      (synCkqrel (synCwppqkrelkernel)) p0016
  have p0018 :=
    @gMpbid
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (synCopk (.cv x) (.cv y)))
        (synCkqrel (synCwppqkrelkernel)))
      p0012 p0017
  have p0020 := @gVex x
  have p0021 := @gVex y
  have p0022 :=
    @gWppqkrelkernelpointbrndv (synCop A B) (.cv x) (.cv y) p0000 p0020 p0021
  have p0023 :=
    @gBiimpi
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (synCopk (.cv x) (.cv y)))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (synCop A B) (synCop (.cv x) (.cv y))) p0022
  have p0024 :=
    @gSyl
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (synCopk (.cv x) (.cv y)))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (synCop A B) (synCop (.cv x) (.cv y))) p0018 p0023
  have p0025 := @gOpth A B (.cv x) (.cv y)
  have p0026 :=
    @gBiimpi (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
      (synWa (.classEq A (.cv x)) (.classEq B (.cv y))) p0025
  have p0027 :=
    @gSyl
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
      (synWa (.classEq A (.cv x)) (.classEq B (.cv y))) p0024 p0026
  have p0028 := @gOpkeq12 A B (.cv x) (.cv y)
  have p0029 :=
    @gSyl
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (synWa (.classEq A (.cv x)) (.classEq B (.cv y)))
      (.classEq (synCopk A B) (synCopk (.cv x) (.cv y))) p0027 p0028
  have p0030 :=
    @gEqcomd
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (synCopk A B) (synCopk (.cv x) (.cv y)) p0029
  have p0031 :=
    @gEqtrd
      (synWa (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
          (synCkqrel (synCwppqkrelkernel))) (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      D (synCopk (.cv x) (.cv y)) (synCopk A B) p0011 p0030
  have p0032 :=
    @gEx
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (synWa (.classEq D (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq D (synCopk A B)) p0031
  have p0033 :=
    @gExlimd
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (synWa (.classEq D (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (.classEq D (synCopk A B)) y p0007 p0008 p0032
  have p0034 :=
    @gExlimd
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (synWex y (synWa (.classEq D (synCopk (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (.classEq D (synCopk A B)) x p0005 p0006 p0033
  have p0035 :=
    @gMpd
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (synWex x (synWex y (synWa (.classEq D (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      (.classEq D (synCopk A B)) p0004 p0034
  have p0036 := @gEqid (synCop A B)
  have p0038 :=
    @gWppqkrelkernelpointbrndv (synCop A B) A B p0000 hyp_wppqkrelcanonicalfiberndv_1
      hyp_wppqkrelcanonicalfiberndv_2
  have p0039 :=
    @gMpbir
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (synCopk A B))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (synCop A B) (synCop A B)) p0036 p0038
  have p0040 :=
    @gA1i
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (synCopk A B))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq D (synCopk A B)) p0039
  have p0041 := @gId (.classEq D (synCopk A B))
  have p0042 :=
    @gOpeq2d (.classEq D (synCopk A B)) D (synCopk A B)
      (synCsn (synCsn (synCop A B))) p0041
  have p0043 :=
    @gEleq1d (.classEq D (synCopk A B)) (synCop (synCsn (synCsn (synCop A B))) D)
      (synCop (synCsn (synCsn (synCop A B))) (synCopk A B))
      (synCkqrel (synCwppqkrelkernel)) p0042
  have p0044 :=
    @gMpbird (.classEq D (synCopk A B))
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (synCopk A B))
        (synCkqrel (synCwppqkrelkernel)))
      p0040 p0043
  have p0045 :=
    @gImpbii
      (.classMem (synCop (synCsn (synCsn (synCop A B))) D)
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq D (synCopk A B)) p0035 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelcanonicaleu`. -/
@[expose]
noncomputable def gWppqkrelcanonicaleu (A : Class) (B : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv)
    (hyp_wppqkrelcanonicaleu_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_wppqkrelcanonicaleu_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWeu d (.classMem (synCop (synCsn (synCsn (synCop A B))) (.cv d))
          (synCkqrel (synCwppqkrelkernel)))) :=
  by
  have dv_cache_0001 : d ∉ ((synCopk A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, dv_A_d, dv_B_d, or_false, not_false_eq_true])
  have p0000 := @gOpkex A B
  have p0001 := @gEueq1 d (synCopk A B) dv_cache_0001 p0000
  have p0002 := @gVex d
  have p0003 :=
    @gWppqkrelcanonicalfiberndv A B (.cv d) hyp_wppqkrelcanonicaleu_1
      hyp_wppqkrelcanonicaleu_2 p0002
  have p0004 :=
    @gEubii
      (.classMem (synCop (synCsn (synCsn (synCop A B))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      (.classEq (.cv d) (synCopk A B)) d p0003
  have p0005 :=
    @gMpbir
      (synWeu d (.classMem (synCop (synCsn (synCsn (synCop A B))) (.cv d))
          (synCkqrel (synCwppqkrelkernel))))
      (synWeu d (.classEq (.cv d) (synCopk A B))) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelresfnndv`. -/
@[expose]
noncomputable def gWppqkrelresfnndv (A : Class) (B : Class)
    (_hyp_wppqkrelresfnndv_1 : Nominal.NPrf (.classMem A (synCvv)))
    (_hyp_wppqkrelresfnndv_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWfn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
        (synCpw1 (synCpw1 (synCxp A B)))) :=
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
      ((synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
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
      ((synWeu d
          (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))).fv :=
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
      ((synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
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
      ((synWeu d
          (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))).fv :=
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
      ((synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
              (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
          (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))).fv :=
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
      ((synWeu d
          (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))).fv :=
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
    u ∉ ((Wff.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))).fv :=
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
  have dv_cache_0019 : s ∉ ((synCpw1 (synCpw1 (synCxp A B)))).fv :=
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
  have dv_cache_0020 : d ∉ ((synCpw1 (synCpw1 (synCxp A B)))).fv :=
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
  have dv_cache_0021 : s ∉ ((synCkqrel (synCwppqkrelkernel))).fv :=
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
  have dv_cache_0022 : d ∉ ((synCkqrel (synCwppqkrelkernel))).fv :=
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
  have p0000 := @gElpw12 u (.cv s) (synCxp A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpi (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (synWrex u (synCxp A B) (.classEq (.cv s) (synCsn (synCsn (.cv u))))) p0000
  have p0002 :=
    @gSimpl
      (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
        (.classMem (.cv u) (synCxp A B)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u))))
  have p0003 :=
    @gSimpr (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (.classMem (.cv u) (synCxp A B))
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
        (.classMem (.cv u) (synCxp A B)))
      (.classMem (.cv u) (synCxp A B)) p0002 p0003
  have p0005 :=
    @gElxp a b (.cv u) A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0006 :=
    @gBiimpi (.classMem (.cv u) (synCxp A B))
      (synWex a (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0005
  have p0007 :=
    @gSyl
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (.classMem (.cv u) (synCxp A B))
      (synWex a (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      p0004 p0006
  have p0008 :=
    @gNfv
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      a dv_cache_0010
  have p0009 :=
    @gNfv
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      a dv_cache_0011
  have p0010 :=
    @gNfv
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      b dv_cache_0012
  have p0011 :=
    @gNfv
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      b dv_cache_0013
  have p0012 := @gVex a
  have p0013 := @gVex b
  have p0014 :=
    @gWppqkrelcanonicaleu (.cv a) (.cv b) d dv_cache_0014 dv_cache_0015 p0012 p0013
  have p0015 :=
    @gA1i
      (synWeu d (.classMem (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
          (synCkqrel (synCwppqkrelkernel))))
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      p0014
  have p0016 :=
    @gNfv
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      d dv_cache_0016
  have p0017 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0018 :=
    @gSimpr
      (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
        (.classMem (.cv u) (synCxp A B)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u))))
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (.classEq (.cv s) (synCsn (synCsn (.cv u)))) p0017 p0018
  have p0020 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
  have p0021 :=
    @gSimpl (.classEq (.cv u) (synCop (.cv a) (.cv b)))
      (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (.classEq (.cv u) (synCop (.cv a) (.cv b))) p0020 p0021
  have p0023 := @gSneq (.cv u) (synCop (.cv a) (.cv b))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (.cv u) (synCop (.cv a) (.cv b)))
      (.classEq (synCsn (.cv u)) (synCsn (synCop (.cv a) (.cv b)))) p0022 p0023
  have p0025 := @gSneq (synCsn (.cv u)) (synCsn (synCop (.cv a) (.cv b)))
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classEq (synCsn (.cv u)) (synCsn (synCop (.cv a) (.cv b))))
      (.classEq (synCsn (synCsn (.cv u))) (synCsn (synCsn (synCop (.cv a) (.cv b)))))
      p0024 p0025
  have p0027 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (synCsn (synCsn (.cv u))) (synCsn (synCsn (synCop (.cv a) (.cv b))))
      p0019 p0026
  have p0028 :=
    @gOpeq1d
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.cv s) (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d) p0027
  have p0029 :=
    @gEleq1d
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synCop (.cv s) (.cv d))
      (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
      (synCkqrel (synCwppqkrelkernel)) p0028
  have p0030 :=
    @gEubid
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel)))
      (.classMem (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
        (synCkqrel (synCwppqkrelkernel)))
      d p0016 p0029
  have p0031 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
            (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
        (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      (synWeu d (.classMem (synCop (synCsn (synCsn (synCop (.cv a) (.cv b)))) (.cv d))
          (synCkqrel (synCwppqkrelkernel))))
      p0015 p0030
  have p0032 :=
    @gEx
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      p0031
  have p0033 :=
    @gExlimd
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      b p0010 p0011 p0032
  have p0034 :=
    @gExlimd
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
          (synWa (.classMem (.cv a) A) (.classMem (.cv b) B))))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      a p0008 p0009 p0033
  have p0035 :=
    @gMpd
      (synWa (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
          (.classMem (.cv u) (synCxp A B))) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWex a (synWex b (synWa (.classEq (.cv u) (synCop (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) A) (.classMem (.cv b) B)))))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      p0007 p0034
  have p0036 :=
    @gEx
      (synWa (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
        (.classMem (.cv u) (synCxp A B)))
      (.classEq (.cv s) (synCsn (synCsn (.cv u))))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      p0035
  have p0037 :=
    @gRexlimdva (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (.classEq (.cv s) (synCsn (synCsn (.cv u))))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      u (synCxp A B) dv_cache_0017 dv_cache_0018 p0036
  have p0038 :=
    @gMpd (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (synWrex u (synCxp A B) (.classEq (.cv s) (synCsn (synCsn (.cv u)))))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      p0001 p0037
  have p0039 :=
    (Nominal.biimpRefl (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d)))
  have p0040 :=
    @gEubii (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))
      (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))) d p0039
  have p0041 :=
    @gA1i
      (synWb (synWeu d (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d)))
        (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel)))))
      (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B)))) p0040
  have p0042 :=
    @gMpbird (.classMem (.cv s) (synCpw1 (synCpw1 (synCxp A B))))
      (synWeu d (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d)))
      (synWeu d (.classMem (synCop (.cv s) (.cv d)) (synCkqrel (synCwppqkrelkernel))))
      p0038 p0041
  have p0043 :=
    @gRgen (synWeu d (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))) s
      (synCpw1 (synCpw1 (synCxp A B))) p0042
  have p0044 :=
    @gFnres s d (synCpw1 (synCpw1 (synCxp A B))) (synCkqrel (synCwppqkrelkernel))
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0045 :=
    @gMpbir
      (synWfn (synCres (synCkqrel (synCwppqkrelkernel)) (synCpw1 (synCpw1 (synCxp A B))))
        (synCpw1 (synCpw1 (synCxp A B))))
      (synWral s (synCpw1 (synCpw1 (synCxp A B)))
        (synWeu d (synWbr (.cv s) (synCkqrel (synCwppqkrelkernel)) (.cv d))))
      p0043 p0044
  exact p0045


end NFChoice.DirectNominalPrf.WPPReplay

end
