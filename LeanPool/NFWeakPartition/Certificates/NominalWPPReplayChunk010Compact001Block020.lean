/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block019

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part065`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_brswap2 (A : Class) (B : Class) (C : Class)
    (hyp_br1st_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_brswap_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cswap) (syn_cop B C)) (.classEq A (syn_cop C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : z ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv y) (syn_cop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_B, fresh_z_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Wff.classEq (.cv y) (syn_cop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_B, fresh_w_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0005 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0006 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0007 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0008 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq A (syn_cop C B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_C, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Wff.classEq A (syn_cop (.cv z) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z, fresh_w_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0011 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0012 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0013 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0014 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0015 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0016 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0017 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0018 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((syn_cop B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((syn_cop B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Wff.classEq A (syn_cop C B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ ((Wff.classEq A (syn_cop C B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_brex A (syn_cop B C) (syn_cswap)
  have p0001 :=
    @g_simpld (syn_wbr A (syn_cswap) (syn_cop B C)) (.classMem A (syn_cvv))
      (.classMem (syn_cop B C) (syn_cvv)) p0000
  have p0002 := @g_opex C B hyp_brswap_2 hyp_br1st_1
  have p0003 := @g_eleq1 A (syn_cop C B) (syn_cvv)
  have p0004 :=
    @g_mpbiri (.classEq A (syn_cop C B)) (.classMem A (syn_cvv))
      (.classMem (syn_cop C B) (syn_cvv)) p0002 p0003
  have p0005 := @g_opex B C hyp_br1st_1 hyp_brswap_2
  have p0006 := @g_eqeq1 (.cv x) A (syn_cop (.cv z) (.cv w))
  have p0007 :=
    @g_anbi1d (.classEq (.cv x) A) (.classEq (.cv x) (syn_cop (.cv z) (.cv w)))
      (.classEq A (syn_cop (.cv z) (.cv w))) (.classEq (.cv y) (syn_cop (.cv w) (.cv z)))
      p0006
  have p0008 :=
    @g_n_2exbidv (.classEq (.cv x) A)
      (syn_wa (.classEq (.cv x) (syn_cop (.cv z) (.cv w)))
        (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))
      z w dv_cache_0001 dv_cache_0002 p0007
  have p0009 := @g_eqeq1 (.cv y) (syn_cop B C) (syn_cop (.cv w) (.cv z))
  have p0010 :=
    @g_anbi2d (.classEq (.cv y) (syn_cop B C))
      (.classEq (.cv y) (syn_cop (.cv w) (.cv z)))
      (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z)))
      (.classEq A (syn_cop (.cv z) (.cv w))) p0009
  have p0011 := @g_eqcom (syn_cop B C) (syn_cop (.cv w) (.cv z))
  have p0012 := @g_opth (.cv w) (.cv z) B C
  have p0013 :=
    @g_bitri (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z)))
      (.classEq (syn_cop (.cv w) (.cv z)) (syn_cop B C))
      (syn_wa (.classEq (.cv w) B) (.classEq (.cv z) C)) p0011 p0012
  have p0014 :=
    @g_anbi1i (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z)))
      (syn_wa (.classEq (.cv w) B) (.classEq (.cv z) C))
      (.classEq A (syn_cop (.cv z) (.cv w))) p0013
  have p0015 :=
    @g_ancom (.classEq A (syn_cop (.cv z) (.cv w)))
      (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z)))
  have p0016 :=
    (Nominal.biimpRefl (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C)
        (.classEq A (syn_cop (.cv z) (.cv w)))))
  have p0017 :=
    @g_n_3bitr4ri
      (syn_wa (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z)))
        (.classEq A (syn_cop (.cv z) (.cv w))))
      (syn_wa (syn_wa (.classEq (.cv w) B) (.classEq (.cv z) C))
        (.classEq A (syn_cop (.cv z) (.cv w))))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z))))
      (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (syn_cop (.cv z) (.cv w))))
      p0014 p0015 p0016
  have p0018 :=
    @g_syl6bbr (.classEq (.cv y) (syn_cop B C))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (.classEq (syn_cop B C) (syn_cop (.cv w) (.cv z))))
      (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (syn_cop (.cv z) (.cv w))))
      p0010 p0017
  have p0019 :=
    @g_n_2exbidv (.classEq (.cv y) (syn_cop B C))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))
      (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (syn_cop (.cv z) (.cv w))))
      z w dv_cache_0003 dv_cache_0004 p0018
  have p0020 :=
    @g_excom
      (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (syn_cop (.cv z) (.cv w))))
      z w
  have p0021 :=
    @g_syl6bb (.classEq (.cv y) (syn_cop B C))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))))
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C)
            (.classEq A (syn_cop (.cv z) (.cv w))))))
      (syn_wex w (syn_wex z (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C)
            (.classEq A (syn_cop (.cv z) (.cv w))))))
      p0019 p0020
  have p0022 := @g_opeq2 (.cv w) B (.cv z)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv w) B) (syn_cop (.cv z) (.cv w)) (syn_cop (.cv z) B) A p0022
  have p0024 := @g_opeq1 (.cv z) C B
  have p0025 := @g_eqeq2d (.classEq (.cv z) C) (syn_cop (.cv z) B) (syn_cop C B) A p0024
  have p0026 :=
    @g_ceqsex2v (.classEq A (syn_cop (.cv z) (.cv w))) (.classEq A (syn_cop (.cv z) B))
      (.classEq A (syn_cop C B)) w z B C dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 hyp_br1st_1 hyp_brswap_2
      p0023 p0025
  have p0027 :=
    @g_syl6bb (.classEq (.cv y) (syn_cop B C))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))))
      (syn_wex w (syn_wex z (syn_w3a (.classEq (.cv w) B) (.classEq (.cv z) C)
            (.classEq A (syn_cop (.cv z) (.cv w))))))
      (.classEq A (syn_cop C B)) p0021 p0026
  have p0028 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_swap x y z w
      dv_cache_0012 dv_cache_0013 dv_cache_0011 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0029 :=
    @g_brabg
      (syn_wex z (syn_wex w (syn_wa (.classEq (.cv x) (syn_cop (.cv z) (.cv w)))
            (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (.classEq (.cv y) (syn_cop (.cv w) (.cv z))))))
      (.classEq A (syn_cop C B)) x y A (syn_cop B C) (syn_cvv) (syn_cvv) (syn_cswap)
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0014 p0008 p0027 p0028
  have p0030 :=
    @g_mpan2 (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv))
      (syn_wb (syn_wbr A (syn_cswap) (syn_cop B C)) (.classEq A (syn_cop C B))) p0005
      p0029
  have p0031 :=
    @g_pm5_21nii (syn_wbr A (syn_cswap) (syn_cop B C)) (.classMem A (syn_cvv))
      (.classEq A (syn_cop C B)) p0001 p0004 p0030
  exact p0031

@[expose]
noncomputable def g_opabid2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_copab x y (.classMem (syn_cop (.cv x) (.cv y)) A)) A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_cop (.cv z) (.cv w)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, dv_A_x, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classMem (syn_cop (.cv z) (.cv w)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, dv_A_y, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : z ∉ ((syn_copab x y (.classMem (syn_cop (.cv x) (.cv y)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_copab x y (.classMem (syn_cop (.cv x) (.cv y)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0011 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0012 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 := @g_vex z
  have p0001 := @g_vex w
  have p0002 := @g_opeq1 (.cv x) (.cv z) (.cv y)
  have p0003_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (.cv z) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @g_eleq1d (.objEq x z) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv z) (.cv y)) A
      p0003_e00_recanon
  have p0004 := @g_opeq2 (.cv y) (.cv w) (.cv z)
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (.classEq (syn_cop (.cv z) (.cv y)) (syn_cop (.cv z) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_eleq1d (.objEq y w) (syn_cop (.cv z) (.cv y)) (syn_cop (.cv z) (.cv w)) A
      p0005_e00_recanon
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv z) (.cv y)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0006_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv w)) (syn_wb (.classMem (syn_cop (.cv z) (.cv y)) A)
          (.classMem (syn_cop (.cv z) (.cv w)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_opelopab (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (.cv z) (.cv y)) A) (.classMem (syn_cop (.cv z) (.cv w)) A) x y
      (.cv z) (.cv w) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001 p0006_e02_recanon
      p0006_e03_recanon
  have p0007 :=
    @g_eqrelriv z w (syn_copab x y (.classMem (syn_cop (.cv x) (.cv y)) A)) A
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0006
  exact p0007

@[expose]
noncomputable def g_inopab (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_copab x y ph) (syn_copab x y ps))
        (syn_copab x y (syn_wa ph ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : z ∉ ((syn_cin (syn_copab x y ph) (syn_copab x y ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x,
          fresh_z_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_cin (syn_copab x y ph) (syn_copab x y ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_ph, fresh_w_ne_x,
          fresh_w_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_copab x y (syn_wa ph ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_ph, fresh_z_not_ps,
          fresh_z_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_copab x y (syn_wa ph ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_ph, fresh_w_not_ps,
          fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 := @g_sbcan (syn_wsbc (.cv w) y ph) (syn_wsbc (.cv w) y ps) x (.cv z)
  have p0001 := @g_sbcan ph ps y (.cv w)
  have p0002 :=
    @g_sbcbii (syn_wsbc (.cv w) y (syn_wa ph ps))
      (syn_wa (syn_wsbc (.cv w) y ph) (syn_wsbc (.cv w) y ps)) x (.cv z) p0001
  have p0003 := @g_opelopabsb ph x y (.cv z) (.cv w) dv_cache_0001 dv_cache_0002
  have p0004 := @g_opelopabsb ps x y (.cv z) (.cv w) dv_cache_0001 dv_cache_0002
  have p0005 :=
    @g_anbi12i (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
      (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y ph))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ps))
      (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y ps)) p0003 p0004
  have p0006 :=
    @g_n_3bitr4ri
      (syn_wsbc (.cv z) x (syn_wa (syn_wsbc (.cv w) y ph) (syn_wsbc (.cv w) y ps)))
      (syn_wa (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y ph))
        (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y ps)))
      (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y (syn_wa ph ps)))
      (syn_wa (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
        (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ps)))
      p0000 p0002 p0005
  have p0007 := @g_elin (syn_cop (.cv z) (.cv w)) (syn_copab x y ph) (syn_copab x y ps)
  have p0008 :=
    @g_opelopabsb (syn_wa ph ps) x y (.cv z) (.cv w) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
        (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ps)))
      (syn_wsbc (.cv z) x (syn_wsbc (.cv w) y (syn_wa ph ps)))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_cin (syn_copab x y ph) (syn_copab x y ps)))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y (syn_wa ph ps))) p0006 p0007
      p0008
  have p0010 :=
    @g_eqrelriv z w (syn_cin (syn_copab x y ph) (syn_copab x y ps))
      (syn_copab x y (syn_wa ph ps)) dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0009
  exact p0010

@[expose]
noncomputable def g_inxp (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cxp A B) (syn_cxp C D)) (syn_cxp (syn_cin A C) (syn_cin B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
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
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0008 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0009 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cin A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cin A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cin B D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cin B D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_D, or_false, not_false_eq_true])
  have p0000 :=
    @g_inopab (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) x y dv_cache_0001
  have p0001 :=
    @g_an4 (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv x) C)
      (.classMem (.cv y) D)
  have p0002 := @g_elin (.cv x) A C
  have p0003 := @g_elin (.cv y) B D
  have p0004 :=
    @g_anbi12i (.classMem (.cv x) (syn_cin A C))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (.classMem (.cv y) (syn_cin B D))
      (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D)) p0002 p0003
  have p0005 :=
    @g_bitr4i
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D)))
      (syn_wa (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv y) (syn_cin B D))) p0001
      p0004
  have p0006 :=
    @g_opabbii
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (syn_wa (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv y) (syn_cin B D))) x y
      p0005
  have p0007 :=
    @g_eqtri
      (syn_cin (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (syn_copab x y (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))))
      (syn_copab x y (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))))
      (syn_copab x y
        (syn_wa (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv y) (syn_cin B D))))
      p0000 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A B
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y C D
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0001
  have p0010 :=
    @g_ineq12i (syn_cxp A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_cxp C D)
      (syn_copab x y (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))) p0008 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y (syn_cin A C)
      (syn_cin B D) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0001
  have p0012 :=
    @g_n_3eqtr4i
      (syn_cin (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (syn_copab x y (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))))
      (syn_copab x y
        (syn_wa (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv y) (syn_cin B D))))
      (syn_cin (syn_cxp A B) (syn_cxp C D)) (syn_cxp (syn_cin A C) (syn_cin B D)) p0007
      p0010 p0011
  exact p0012

@[expose]
noncomputable def g_opabbi2i (ph : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_opabbi2i_1 : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) ph)) :
    Nominal.NPrf (.classEq A (syn_copab x y ph)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_opabid2 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_opabbii (.classMem (syn_cop (.cv x) (.cv y)) A) ph x y hyp_opabbi2i_1
  have p0002 :=
    @g_eqtr3i (syn_copab x y (.classMem (syn_cop (.cv x) (.cv y)) A)) A (syn_copab x y ph)
      p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part066`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ideqg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (syn_wb (syn_wbr A (syn_cid) B) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_brex A B (syn_cid)
  have p0001 :=
    @g_adantl (syn_wbr A (syn_cid) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem B V) p0000
  have p0002 := @g_simpr (.classMem B V) (.classEq A B)
  have p0003 := @g_elex B V
  have p0004 := @g_adantr (.classMem B V) (.classMem B (syn_cvv)) (.classEq A B) p0003
  have p0005 :=
    @g_eqeltrd (syn_wa (.classMem B V) (.classEq A B)) A B (syn_cvv) p0002 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B V) (.classEq A B)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv)) p0005 p0004
  have p0007 := @g_eqeq1 (.cv x) A (.cv y)
  have p0008 := @g_eqeq2 (.cv y) B A
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_id x y dv_cache_0001
  have p0010_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb (.objEq x y) (.classEq A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0007
  have p0010 :=
    @g_brabg (.objEq x y) (.classEq A (.cv y)) (.classEq A B) x y A B (syn_cvv) (syn_cvv)
      (syn_cid) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0010_e00_recanon p0008 p0009
  have p0011 :=
    @g_pm5_21nd (.classMem B V) (syn_wbr A (syn_cid) B) (.classEq A B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0001 p0006 p0010
  exact p0011

@[expose]
noncomputable def g_ideq (A : Class) (B : Class)
    (hyp_ideq_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cid) B) (.classEq A B)) :=
  by
  have p0000 := @g_ideqg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_ideq_1 p0000
  exact p0001

@[expose]
noncomputable def g_ididg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wbr A (syn_cid) A)) :=
  by
  have p0000 := @g_eqid A
  have p0001 := @g_ideqg A A V
  have p0002 :=
    @g_mpbiri (.classMem A V) (syn_wbr A (syn_cid) A) (.classEq A A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_coss1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_ccom A C) (syn_ccom B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((syn_wss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0008 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0009 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0010 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0012 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0014 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0015 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @g_id (syn_wss A B)
  have p0001 := @g_ssbrd (syn_wss A B) A B (.cv y) (.cv z) p0000
  have p0002 :=
    @g_anim2d (syn_wss A B) (syn_wbr (.cv y) A (.cv z)) (syn_wbr (.cv y) B (.cv z))
      (syn_wbr (.cv x) C (.cv y)) p0001
  have p0003 :=
    @g_eximdv (syn_wss A B)
      (syn_wa (syn_wbr (.cv x) C (.cv y)) (syn_wbr (.cv y) A (.cv z)))
      (syn_wa (syn_wbr (.cv x) C (.cv y)) (syn_wbr (.cv y) B (.cv z))) y dv_cache_0001
      p0002
  have p0004 :=
    @g_ssopab2dv (syn_wss A B)
      (syn_wex y (syn_wa (syn_wbr (.cv x) C (.cv y)) (syn_wbr (.cv y) A (.cv z))))
      (syn_wex y (syn_wa (syn_wbr (.cv x) C (.cv y)) (syn_wbr (.cv y) B (.cv z)))) x z
      dv_cache_0002 dv_cache_0003 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x z y A C
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x z y B C
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0007 :=
    @g_n_3sstr4g (syn_wss A B)
      (syn_copab x z
        (syn_wex y (syn_wa (syn_wbr (.cv x) C (.cv y)) (syn_wbr (.cv y) A (.cv z)))))
      (syn_copab x z
        (syn_wex y (syn_wa (syn_wbr (.cv x) C (.cv y)) (syn_wbr (.cv y) B (.cv z)))))
      (syn_ccom A C) (syn_ccom B C) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_coss2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_ccom C A) (syn_ccom C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((syn_wss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0005 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0012 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0014 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0015 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @g_id (syn_wss A B)
  have p0001 := @g_ssbrd (syn_wss A B) A B (.cv x) (.cv y) p0000
  have p0002 :=
    @g_anim1d (syn_wss A B) (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))
      (syn_wbr (.cv y) C (.cv z)) p0001
  have p0003 :=
    @g_eximdv (syn_wss A B)
      (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv y) C (.cv z)))
      (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) C (.cv z))) y dv_cache_0001
      p0002
  have p0004 :=
    @g_ssopab2dv (syn_wss A B)
      (syn_wex y (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv y) C (.cv z))))
      (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) C (.cv z)))) x z
      dv_cache_0002 dv_cache_0003 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x z y C A
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x z y C B
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0007 :=
    @g_n_3sstr4g (syn_wss A B)
      (syn_copab x z
        (syn_wex y (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv y) C (.cv z)))))
      (syn_copab x z
        (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) C (.cv z)))))
      (syn_ccom C A) (syn_ccom C B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_coeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ccom A C) (syn_ccom B C))) :=
  by
  have p0000 := @g_coss1 A B C
  have p0001 := @g_coss1 B A C
  have p0002 :=
    @g_anim12i (syn_wss A B) (syn_wss (syn_ccom A C) (syn_ccom B C)) (syn_wss B A)
      (syn_wss (syn_ccom B C) (syn_ccom A C)) p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 := @g_eqss (syn_ccom A C) (syn_ccom B C)
  have p0005 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (syn_wss (syn_ccom A C) (syn_ccom B C)) (syn_wss (syn_ccom B C) (syn_ccom A C)))
      (.classEq A B) (.classEq (syn_ccom A C) (syn_ccom B C)) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_coeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ccom C A) (syn_ccom C B))) :=
  by
  have p0000 := @g_coss2 A B C
  have p0001 := @g_coss2 B A C
  have p0002 :=
    @g_anim12i (syn_wss A B) (syn_wss (syn_ccom C A) (syn_ccom C B)) (syn_wss B A)
      (syn_wss (syn_ccom C B) (syn_ccom C A)) p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 := @g_eqss (syn_ccom C A) (syn_ccom C B)
  have p0005 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (syn_wss (syn_ccom C A) (syn_ccom C B)) (syn_wss (syn_ccom C B) (syn_ccom C A)))
      (.classEq A B) (.classEq (syn_ccom C A) (syn_ccom C B)) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_coeq1i (A : Class) (B : Class) (C : Class)
    (hyp_coeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_ccom A C) (syn_ccom B C)) :=
  by
  have p0000 := @g_coeq1 A B C
  have p0001 := Nominal.mp hyp_coeq1i_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
