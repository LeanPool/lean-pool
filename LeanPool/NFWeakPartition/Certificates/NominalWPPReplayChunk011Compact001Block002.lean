/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk011Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk011Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dmcoss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdm (syn_ccom A B)) (syn_cdm B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_wbr (.cv x) B (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cdm (syn_ccom A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cdm B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_B,
          not_false_eq_true])
  have p0000 :=
    @g_brco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_exbii (syn_wbr (.cv x) (syn_ccom A B) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))) y p0000
  have p0002 :=
    @g_excom (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))) y z
  have p0003 :=
    @g_bitri (syn_wex y (syn_wbr (.cv x) (syn_ccom A B) (.cv y)))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))))
      (syn_wex z (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))))
      p0001 p0002
  have p0004 := @g_simpl (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))
  have p0005 :=
    @g_exlimiv (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
      (syn_wbr (.cv x) B (.cv z)) y dv_cache_0005 p0004
  have p0006 :=
    @g_eximi (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))
      (syn_wbr (.cv x) B (.cv z)) z p0005
  have p0007 :=
    @g_sylbi (syn_wex y (syn_wbr (.cv x) (syn_ccom A B) (.cv y)))
      (syn_wex z (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))))
      (syn_wex z (syn_wbr (.cv x) B (.cv z))) p0003 p0006
  have p0008 := @g_eldm y (.cv x) (syn_ccom A B) dv_cache_0006 dv_cache_0007
  have p0009 := @g_eldm z (.cv x) B dv_cache_0001 dv_cache_0004
  have p0010 :=
    @g_n_3imtr4i (syn_wex y (syn_wbr (.cv x) (syn_ccom A B) (.cv y)))
      (syn_wex z (syn_wbr (.cv x) B (.cv z))) (.classMem (.cv x) (syn_cdm (syn_ccom A B)))
      (.classMem (.cv x) (syn_cdm B)) p0007 p0008 p0009
  have p0011 :=
    @g_ssriv x (syn_cdm (syn_ccom A B)) (syn_cdm B) dv_cache_0008 dv_cache_0009 p0010
  exact p0011

@[expose]
noncomputable def g_rncoss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_crn (syn_ccom A B)) (syn_crn A)) :=
  by
  have p0000 := @g_dmcoss (syn_ccnv B) (syn_ccnv A)
  have p0001 := @g_dfrn4 (syn_ccom A B)
  have p0002 := @g_cnvco A B
  have p0003 :=
    @g_dmeqi (syn_ccnv (syn_ccom A B)) (syn_ccom (syn_ccnv B) (syn_ccnv A)) p0002
  have p0004 :=
    @g_eqtri (syn_crn (syn_ccom A B)) (syn_cdm (syn_ccnv (syn_ccom A B)))
      (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) p0001 p0003
  have p0005 := @g_dfrn4 A
  have p0006 :=
    @g_n_3sstr4i (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) (syn_cdm (syn_ccnv A))
      (syn_crn (syn_ccom A B)) (syn_crn A) p0000 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_dmcosseq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wss (syn_crn B) (syn_cdm A))
        (.classEq (syn_cdm (syn_ccom A B)) (syn_cdm B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wbr (.cv x) B (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wss (syn_crn B) (syn_cdm A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
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
  have dv_cache_0008 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_ccom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cdm B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cdm (syn_ccom A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_wss (syn_crn B) (syn_cdm A))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_A, or_false, not_false_eq_true])
  have p0000 := @g_dmcoss A B
  have p0001 :=
    @g_a1i (syn_wss (syn_cdm (syn_ccom A B)) (syn_cdm B))
      (syn_wss (syn_crn B) (syn_cdm A)) p0000
  have p0002 := @g_brelrn (.cv x) (.cv y) B
  have p0003 := @g_ssel (syn_crn B) (syn_cdm A) (.cv y)
  have p0004 :=
    @g_syl5 (syn_wbr (.cv x) B (.cv y)) (.classMem (.cv y) (syn_crn B))
      (syn_wss (syn_crn B) (syn_cdm A)) (.classMem (.cv y) (syn_cdm A)) p0002 p0003
  have p0005 := @g_eldm z (.cv y) A dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_syl6ib (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y))
      (.classMem (.cv y) (syn_cdm A)) (syn_wex z (syn_wbr (.cv y) A (.cv z))) p0004 p0005
  have p0007 :=
    @g_ancld (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y))
      (syn_wex z (syn_wbr (.cv y) A (.cv z))) p0006
  have p0008 :=
    @g_n_19_42v (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)) z dv_cache_0003
  have p0009 :=
    @g_syl6ibr (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y))
      (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wex z (syn_wbr (.cv y) A (.cv z))))
      (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))) p0007
      p0008
  have p0010 :=
    @g_eximdv (syn_wss (syn_crn B) (syn_cdm A)) (syn_wbr (.cv x) B (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))) y
      dv_cache_0004 p0009
  have p0011 :=
    @g_brco y (.cv x) (.cv z) A B dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0012 :=
    @g_exbii (syn_wbr (.cv x) (syn_ccom A B) (.cv z))
      (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))) z p0011
  have p0013 :=
    @g_excom (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z))) z y
  have p0014 :=
    @g_bitri (syn_wex z (syn_wbr (.cv x) (syn_ccom A B) (.cv z)))
      (syn_wex z (syn_wex y (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))))
      p0012 p0013
  have p0015 :=
    @g_syl6ibr (syn_wss (syn_crn B) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) B (.cv y)))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv y) A (.cv z)))))
      (syn_wex z (syn_wbr (.cv x) (syn_ccom A B) (.cv z))) p0010 p0014
  have p0016 := @g_eldm y (.cv x) B dv_cache_0005 dv_cache_0008
  have p0017 := @g_eldm z (.cv x) (syn_ccom A B) dv_cache_0009 dv_cache_0010
  have p0018 :=
    @g_n_3imtr4g (syn_wss (syn_crn B) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) B (.cv y)))
      (syn_wex z (syn_wbr (.cv x) (syn_ccom A B) (.cv z))) (.classMem (.cv x) (syn_cdm B))
      (.classMem (.cv x) (syn_cdm (syn_ccom A B))) p0015 p0016 p0017
  have p0019 :=
    @g_ssrdv (syn_wss (syn_crn B) (syn_cdm A)) x (syn_cdm B) (syn_cdm (syn_ccom A B))
      dv_cache_0011 dv_cache_0012 dv_cache_0013 p0018
  have p0020 :=
    @g_eqssd (syn_wss (syn_crn B) (syn_cdm A)) (syn_cdm (syn_ccom A B)) (syn_cdm B) p0001
      p0019
  exact p0020

@[expose]
noncomputable def g_dmcoeq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classEq (syn_cdm A) (syn_crn B))
        (.classEq (syn_cdm (syn_ccom A B)) (syn_cdm B))) :=
  by
  have p0000 := @g_eqimss2 (syn_crn B) (syn_cdm A)
  have p0001 := @g_dmcosseq A B
  have p0002 :=
    @g_syl (.classEq (syn_cdm A) (syn_crn B)) (syn_wss (syn_crn B) (syn_cdm A))
      (.classEq (syn_cdm (syn_ccom A B)) (syn_cdm B)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rncoeq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classEq (syn_cdm A) (syn_crn B))
        (.classEq (syn_crn (syn_ccom A B)) (syn_crn A))) :=
  by
  have p0000 := @g_dmcoeq (syn_ccnv B) (syn_ccnv A)
  have p0001 := (Nominal.classEqRefl (syn_cdm A))
  have p0002 := @g_dfrn4 B
  have p0003 :=
    @g_eqeq12i (syn_cdm A) (syn_crn (syn_ccnv A)) (syn_crn B) (syn_cdm (syn_ccnv B)) p0001
      p0002
  have p0004 := @g_eqcom (syn_crn (syn_ccnv A)) (syn_cdm (syn_ccnv B))
  have p0005 :=
    @g_bitri (.classEq (syn_cdm A) (syn_crn B))
      (.classEq (syn_crn (syn_ccnv A)) (syn_cdm (syn_ccnv B)))
      (.classEq (syn_cdm (syn_ccnv B)) (syn_crn (syn_ccnv A))) p0003 p0004
  have p0006 := @g_dfrn4 (syn_ccom A B)
  have p0007 := @g_cnvco A B
  have p0008 :=
    @g_dmeqi (syn_ccnv (syn_ccom A B)) (syn_ccom (syn_ccnv B) (syn_ccnv A)) p0007
  have p0009 :=
    @g_eqtri (syn_crn (syn_ccom A B)) (syn_cdm (syn_ccnv (syn_ccom A B)))
      (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) p0006 p0008
  have p0010 := @g_dfrn4 A
  have p0011 :=
    @g_eqeq12i (syn_crn (syn_ccom A B)) (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A)))
      (syn_crn A) (syn_cdm (syn_ccnv A)) p0009 p0010
  have p0012 :=
    @g_n_3imtr4i (.classEq (syn_cdm (syn_ccnv B)) (syn_crn (syn_ccnv A)))
      (.classEq (syn_cdm (syn_ccom (syn_ccnv B) (syn_ccnv A))) (syn_cdm (syn_ccnv A)))
      (.classEq (syn_cdm A) (syn_crn B)) (.classEq (syn_crn (syn_ccom A B)) (syn_crn A))
      p0000 p0005 p0011
  exact p0012

@[expose]
noncomputable def g_res0 (A : Class) :
    Nominal.NPrf (.classEq (syn_cres A (syn_c0)) (syn_c0)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cres A (syn_c0)))
  have p0001 := @g_xp0r (syn_cvv)
  have p0002 := @g_ineq2i (syn_cxp (syn_c0) (syn_cvv)) (syn_c0) A p0001
  have p0003 := @g_in0 A
  have p0004 :=
    @g_n_3eqtri (syn_cres A (syn_c0)) (syn_cin A (syn_cxp (syn_c0) (syn_cvv)))
      (syn_cin A (syn_c0)) (syn_c0) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_resundi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cres A (syn_cun B C)) (syn_cun (syn_cres A B) (syn_cres A C))) :=
  by
  have p0000 := @g_xpundir B C (syn_cvv)
  have p0001 :=
    @g_ineq2i (syn_cxp (syn_cun B C) (syn_cvv))
      (syn_cun (syn_cxp B (syn_cvv)) (syn_cxp C (syn_cvv))) A p0000
  have p0002 := @g_indi A (syn_cxp B (syn_cvv)) (syn_cxp C (syn_cvv))
  have p0003 :=
    @g_eqtri (syn_cin A (syn_cxp (syn_cun B C) (syn_cvv)))
      (syn_cin A (syn_cun (syn_cxp B (syn_cvv)) (syn_cxp C (syn_cvv))))
      (syn_cun (syn_cin A (syn_cxp B (syn_cvv))) (syn_cin A (syn_cxp C (syn_cvv)))) p0001
      p0002
  have p0004 := (Nominal.classEqRefl (syn_cres A (syn_cun B C)))
  have p0005 := (Nominal.classEqRefl (syn_cres A B))
  have p0006 := (Nominal.classEqRefl (syn_cres A C))
  have p0007 :=
    @g_uneq12i (syn_cres A B) (syn_cin A (syn_cxp B (syn_cvv))) (syn_cres A C)
      (syn_cin A (syn_cxp C (syn_cvv))) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cin A (syn_cxp (syn_cun B C) (syn_cvv)))
      (syn_cun (syn_cin A (syn_cxp B (syn_cvv))) (syn_cin A (syn_cxp C (syn_cvv))))
      (syn_cres A (syn_cun B C)) (syn_cun (syn_cres A B) (syn_cres A C)) p0003 p0004 p0007
  exact p0008

@[expose]
noncomputable def g_resundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cres (syn_cun A B) C) (syn_cun (syn_cres A C) (syn_cres B C))) :=
  by
  have p0000 := @g_indir A B (syn_cxp C (syn_cvv))
  have p0001 := (Nominal.classEqRefl (syn_cres (syn_cun A B) C))
  have p0002 := (Nominal.classEqRefl (syn_cres A C))
  have p0003 := (Nominal.classEqRefl (syn_cres B C))
  have p0004 :=
    @g_uneq12i (syn_cres A C) (syn_cin A (syn_cxp C (syn_cvv))) (syn_cres B C)
      (syn_cin B (syn_cxp C (syn_cvv))) p0002 p0003
  have p0005 :=
    @g_n_3eqtr4i (syn_cin (syn_cun A B) (syn_cxp C (syn_cvv)))
      (syn_cun (syn_cin A (syn_cxp C (syn_cvv))) (syn_cin B (syn_cxp C (syn_cvv))))
      (syn_cres (syn_cun A B) C) (syn_cun (syn_cres A C) (syn_cres B C)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_dmres (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cres A B)) (syn_cin B (syn_cdm A))) :=
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
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cres A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cdm (syn_cres A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @g_n_19_41v (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B) y dv_cache_0001
  have p0001 := @g_eldm y (.cv x) (syn_cres A B) dv_cache_0002 dv_cache_0003
  have p0002 := @g_brres (.cv x) (.cv y) A B
  have p0003 :=
    @g_exbii (syn_wbr (.cv x) (syn_cres A B) (.cv y))
      (syn_wa (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B)) y p0002
  have p0004 :=
    @g_bitri (.classMem (.cv x) (syn_cdm (syn_cres A B)))
      (syn_wex y (syn_wbr (.cv x) (syn_cres A B) (.cv y)))
      (syn_wex y (syn_wa (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B))) p0001 p0003
  have p0005 := @g_eldm y (.cv x) A dv_cache_0002 dv_cache_0004
  have p0006 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) A (.cv y)))
      (.classMem (.cv x) B) p0005
  have p0007 :=
    @g_n_3bitr4ri (syn_wex y (syn_wa (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) B)))
      (syn_wa (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) B))
      (.classMem (.cv x) (syn_cdm (syn_cres A B)))
      (syn_wa (.classMem (.cv x) (syn_cdm A)) (.classMem (.cv x) B)) p0000 p0004 p0006
  have p0008 :=
    @g_ineqri x (syn_cdm A) B (syn_cdm (syn_cres A B)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0007
  have p0009 := @g_incom (syn_cdm A) B
  have p0010 :=
    @g_eqtr3i (syn_cin (syn_cdm A) B) (syn_cdm (syn_cres A B)) (syn_cin B (syn_cdm A))
      p0008 p0009
  exact p0010

@[expose]
noncomputable def g_ssdmres (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wss A (syn_cdm B)) (.classEq (syn_cdm (syn_cres B A)) A)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wss A (syn_cdm B)))
  have p0001 := @g_dmres B A
  have p0002 := @g_eqeq1i (syn_cdm (syn_cres B A)) (syn_cin A (syn_cdm B)) A p0001
  have p0003 :=
    @g_bitr4i (syn_wss A (syn_cdm B)) (.classEq (syn_cin A (syn_cdm B)) A)
      (.classEq (syn_cdm (syn_cres B A)) A) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_resss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cres A B) A) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cres A B))
  have p0001 := @g_inss1 A (syn_cxp B (syn_cvv))
  have p0002 := @g_eqsstri (syn_cres A B) (syn_cin A (syn_cxp B (syn_cvv))) A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ssres2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cres C A) (syn_cres C B))) :=
  by
  have p0000 := @g_xpss1 A B (syn_cvv)
  have p0001 := @g_sslin (syn_cxp A (syn_cvv)) (syn_cxp B (syn_cvv)) C
  have p0002 :=
    @g_syl (syn_wss A B) (syn_wss (syn_cxp A (syn_cvv)) (syn_cxp B (syn_cvv)))
      (syn_wss (syn_cin C (syn_cxp A (syn_cvv))) (syn_cin C (syn_cxp B (syn_cvv)))) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (syn_cres C A))
  have p0004 := (Nominal.classEqRefl (syn_cres C B))
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cin C (syn_cxp A (syn_cvv)))
      (syn_cin C (syn_cxp B (syn_cvv))) (syn_cres C A) (syn_cres C B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_ssreseq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss (syn_cdm A) B) (.classEq (syn_cres A B) A)) :=
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cres A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cres A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wss (syn_cdm A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wss (syn_cdm A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_resss A B
  have p0001 := @g_a1i (syn_wss (syn_cres A B) A) (syn_wss (syn_cdm A) B) p0000
  have p0002 := @g_opeldm (.cv x) (.cv y) A
  have p0003 := @g_ssel (syn_cdm A) B (.cv x)
  have p0004 :=
    @g_syl5 (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) (syn_cdm A))
      (syn_wss (syn_cdm A) B) (.classMem (.cv x) B) p0002 p0003
  have p0005 :=
    @g_ancld (syn_wss (syn_cdm A) B) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (.cv x) B) p0004
  have p0006 := @g_opelres (.cv x) (.cv y) A B
  have p0007 :=
    @g_syl6ibr (syn_wss (syn_cdm A) B) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) B))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cres A B)) p0005 p0006
  have p0008 :=
    @g_relssdv (syn_wss (syn_cdm A) B) x y A (syn_cres A B) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 := @g_eqssd (syn_wss (syn_cdm A) B) (syn_cres A B) A p0001 p0008
  exact p0009

@[expose]
noncomputable def g_resopab (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cres (syn_copab x y ph) A)
        (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) :=
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
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := (Nominal.classEqRefl (syn_cres (syn_copab x y ph) A))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 := @g_vex y
  have p0003 := @g_biantru (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_opabbii (.classMem (.cv x) A)
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cvv))) x y p0003
  have p0005 :=
    @g_eqtr4i (syn_cxp A (syn_cvv))
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cvv))))
      (syn_copab x y (.classMem (.cv x) A)) p0001 p0004
  have p0006 :=
    @g_ineq2i (syn_cxp A (syn_cvv)) (syn_copab x y (.classMem (.cv x) A))
      (syn_copab x y ph) p0005
  have p0007 := @g_incom (syn_copab x y ph) (syn_copab x y (.classMem (.cv x) A))
  have p0008 :=
    @g_eqtri (syn_cin (syn_copab x y ph) (syn_cxp A (syn_cvv)))
      (syn_cin (syn_copab x y ph) (syn_copab x y (.classMem (.cv x) A)))
      (syn_cin (syn_copab x y (.classMem (.cv x) A)) (syn_copab x y ph)) p0006 p0007
  have p0009 := @g_inopab (.classMem (.cv x) A) ph x y dv_cache_0005
  have p0010 :=
    @g_n_3eqtri (syn_cres (syn_copab x y ph) A)
      (syn_cin (syn_copab x y ph) (syn_cxp A (syn_cvv)))
      (syn_cin (syn_copab x y (.classMem (.cv x) A)) (syn_copab x y ph))
      (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) p0000 p0008 p0009
  exact p0010

@[expose]
noncomputable def g_iss (A : Class) :
    Nominal.NPrf
      (syn_wb (syn_wss A (syn_cid)) (.classEq A (syn_cres (syn_cid) (syn_cdm A)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
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
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classMem (syn_cop (.cv x) (.cv x)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wss A (syn_cid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cres (syn_cid) (syn_cdm A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cres (syn_cid) (syn_cdm A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wss A (syn_cid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_ssel A (syn_cid) (syn_cop (.cv x) (.cv y))
  have p0001 := @g_opeldm (.cv x) (.cv y) A
  have p0002 :=
    @g_a1i (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) (syn_cdm A)))
      (syn_wss A (syn_cid)) p0001
  have p0003 :=
    @g_jcad (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A))
      p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y)))
  have p0005 := @g_vex y
  have p0006 := @g_ideq (.cv x) (.cv y) p0005
  have p0007_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))
      (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) p0004 p0007_e01_recanon
  have p0008 :=
    @g_anbi1i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.objEq x y)
      (.classMem (.cv x) (syn_cdm A)) p0007
  have p0009 := @g_eldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0010 :=
    @g_syl6ib (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.objEq x y) p0000 p0007
  have p0011 := @g_opeq2 (.cv x) (.cv y) (.cv x)
  have p0012_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (.classEq (syn_cop (.cv x) (.cv x)) (syn_cop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @g_eleq1d (.objEq x y) (syn_cop (.cv x) (.cv x)) (syn_cop (.cv x) (.cv y)) A
      p0012_e00_recanon
  have p0013 :=
    @g_biimprd (.objEq x y) (.classMem (syn_cop (.cv x) (.cv x)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) A) p0012
  have p0014 :=
    @g_syli (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wss A (syn_cid)) (.objEq x y)
      (.classMem (syn_cop (.cv x) (.cv x)) A) p0010 p0013
  have p0015 :=
    @g_exlimdv (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (.cv x) (.cv x)) A) y dv_cache_0003 dv_cache_0004 p0014
  have p0016 :=
    @g_syl5bi (.classMem (.cv x) (syn_cdm A))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) (syn_wss A (syn_cid))
      (.classMem (syn_cop (.cv x) (.cv x)) A) p0009 p0015
  have p0017 :=
    @g_biimpd (.objEq x y) (.classMem (syn_cop (.cv x) (.cv x)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) A) p0012
  have p0018 :=
    @g_syl9 (syn_wss A (syn_cid)) (.classMem (.cv x) (syn_cdm A))
      (.classMem (syn_cop (.cv x) (.cv x)) A) (.objEq x y)
      (.classMem (syn_cop (.cv x) (.cv y)) A) p0016 p0017
  have p0019 :=
    @g_imp3a (syn_wss A (syn_cid)) (.objEq x y) (.classMem (.cv x) (syn_cdm A))
      (.classMem (syn_cop (.cv x) (.cv y)) A) p0018
  have p0020 :=
    @g_syl5bi
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A)))
      (syn_wa (.objEq x y) (.classMem (.cv x) (syn_cdm A))) (syn_wss A (syn_cid))
      (.classMem (syn_cop (.cv x) (.cv y)) A) p0008 p0019
  have p0021 :=
    @g_impbid (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A)))
      p0003 p0020
  have p0022 := @g_opelres (.cv x) (.cv y) (syn_cid) (syn_cdm A)
  have p0023 :=
    @g_syl6bbr (syn_wss A (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (.cv x) (syn_cdm A)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cres (syn_cid) (syn_cdm A))) p0021 p0022
  have p0024 :=
    @g_eqrelrdv (syn_wss A (syn_cid)) x y A (syn_cres (syn_cid) (syn_cdm A)) dv_cache_0005
      dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0004 dv_cache_0009
      p0023
  have p0025 := @g_resss (syn_cid) (syn_cdm A)
  have p0026 := @g_sseq1 A (syn_cres (syn_cid) (syn_cdm A)) (syn_cid)
  have p0027 :=
    @g_mpbiri (.classEq A (syn_cres (syn_cid) (syn_cdm A))) (syn_wss A (syn_cid))
      (syn_wss (syn_cres (syn_cid) (syn_cdm A)) (syn_cid)) p0025 p0026
  have p0028 :=
    @g_impbii (syn_wss A (syn_cid)) (.classEq A (syn_cres (syn_cid) (syn_cdm A))) p0024
      p0027
  exact p0028

@[expose]
noncomputable def g_resopab2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wss A B)
        (.classEq (syn_cres (syn_copab x y (syn_wa (.classMem (.cv x) B) ph)) A)
          (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))) :=
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
  have dv_cache_0004 : x ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          dv_A_y, dv_B_y, or_false, not_false_eq_true])
  have p0000 :=
    @g_resopab (syn_wa (.classMem (.cv x) B) ph) x y A dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 := @g_ssel A B (.cv x)
  have p0002 := @g_pm4_71 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0003 :=
    @g_sylib (syn_wss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0001 p0002
  have p0004 :=
    @g_anbi1d (syn_wss A B) (.classMem (.cv x) A)
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0003
  have p0005 := @g_anass (.classMem (.cv x) A) (.classMem (.cv x) B) ph
  have p0006 :=
    @g_syl6rbb (syn_wss A B) (syn_wa (.classMem (.cv x) A) ph)
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) ph)
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) ph)) p0004 p0005
  have p0007 :=
    @g_opabbidv (syn_wss A B)
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) ph))
      (syn_wa (.classMem (.cv x) A) ph) x y dv_cache_0004 dv_cache_0005 p0006
  have p0008 :=
    @g_syl5eq (syn_wss A B) (syn_cres (syn_copab x y (syn_wa (.classMem (.cv x) B) ph)) A)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) B) ph)))
      (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_dmresi (A : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cres (syn_cid) A)) A) :=
  by
  have p0000 := @g_ssv A
  have p0001 := @g_dmi
  have p0002 := @g_sseqtr4i A (syn_cvv) (syn_cdm (syn_cid)) p0000 p0001
  have p0003 := @g_ssdmres A (syn_cid)
  have p0004 :=
    @g_mpbi (syn_wss A (syn_cdm (syn_cid))) (.classEq (syn_cdm (syn_cres (syn_cid) A)) A)
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_resid (A : Class) :
    Nominal.NPrf (.classEq (syn_cres A (syn_cvv)) A) :=
  by
  have p0000 := @g_ssv (syn_cdm A)
  have p0001 := @g_ssreseq A (syn_cvv)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_imadmrn (A : Class) :
    Nominal.NPrf (.classEq (syn_cima A (syn_cdm A)) (syn_crn A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ ((syn_cdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := (Nominal.biimpRefl (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y))))
  have p0001 := @g_breldm (.cv x) (.cv y) A
  have p0002 :=
    @g_pm4_71ri (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) (syn_cdm A)) p0001
  have p0003 :=
    @g_exbii (syn_wbr (.cv x) A (.cv y))
      (syn_wa (.classMem (.cv x) (syn_cdm A)) (syn_wbr (.cv x) A (.cv y))) x p0002
  have p0004 :=
    @g_bitr4i (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y)))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_cdm A)) (syn_wbr (.cv x) A (.cv y))))
      (syn_wex x (syn_wbr (.cv x) A (.cv y))) p0000 p0003
  have p0005 :=
    @g_abbii (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y)))
      (syn_wex x (syn_wbr (.cv x) A (.cv y))) y p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x A
      (syn_cdm A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 := @g_dfrn2 x y A dv_cache_0002 dv_cache_0001 dv_cache_0006
  have p0008 :=
    @g_n_3eqtr4i (.cab y (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y))))
      (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_cima A (syn_cdm A))
      (syn_crn A) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_imassrn (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cima A B) (syn_crn A)) :=
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_simpr (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)
  have p0001 :=
    @g_eximi (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))
      (.classMem (syn_cop (.cv x) (.cv y)) A) x p0000
  have p0002 :=
    @g_ss2abi
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)))
      (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) y p0001
  have p0003 :=
    @g_dfima4 x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0004 := @g_dfrn3 x y A dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0005 :=
    @g_n_3sstr4i
      (.cab y (syn_wex x
          (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))))
      (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A))) (syn_cima A B)
      (syn_crn A) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_imai (A : Class) : Nominal.NPrf (.classEq (syn_cima (syn_cid) A) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cid)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv y) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @g_dfima4 x y (syn_cid) A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y)))
  have p0002 := @g_vex y
  have p0003 := @g_ideq (.cv x) (.cv y) p0002
  have p0004 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))
      (syn_wbr (.cv x) (syn_cid) (.cv y)) (.classEq (.cv x) (.cv y)) p0001 p0003
  have p0005 :=
    @g_anbi2i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classEq (.cv x) (.cv y))
      (.classMem (.cv x) A) p0004
  have p0006 := @g_ancom (.classMem (.cv x) A) (.classEq (.cv x) (.cv y))
  have p0007 :=
    @g_bitri
      (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)))
      (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) (.cv y)))
      (syn_wa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)) p0005 p0006
  have p0008 :=
    @g_exbii
      (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)))
      (syn_wa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)) x p0007
  have p0009 := @g_eleq1 (.cv x) (.cv y) A
  have p0010 :=
    @g_ceqsexv (.classMem (.cv x) A) (.classMem (.cv y) A) x (.cv y) dv_cache_0006
      dv_cache_0007 p0002 p0009
  have p0011 :=
    @g_bitri
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))))
      (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)))
      (.classMem (.cv y) A) p0008 p0010
  have p0012 :=
    @g_abbii
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))))
      (.classMem (.cv y) A) y p0011
  have p0013 := @g_abid2 y A dv_cache_0004
  have p0014 :=
    @g_n_3eqtri (syn_cima (syn_cid) A)
      (.cab y (syn_wex x
          (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)))))
      (.cab y (.classMem (.cv y) A)) A p0000 p0012 p0013
  exact p0014

@[expose]
noncomputable def g_ima0 (A : Class) :
    Nominal.NPrf (.classEq (syn_cima A (syn_c0)) (syn_c0)) :=
  by
  have p0000 := @g_dfima3 A (syn_c0)
  have p0001 := @g_res0 A
  have p0002 := @g_rneqi (syn_cres A (syn_c0)) (syn_c0) p0001
  have p0003 := @g_rn0
  have p0004 :=
    @g_n_3eqtri (syn_cima A (syn_c0)) (syn_crn (syn_cres A (syn_c0))) (syn_crn (syn_c0))
      (syn_c0) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_cnvimass (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cima (syn_ccnv A) B) (syn_cdm A)) :=
  by
  have p0000 := @g_imassrn (syn_ccnv A) B
  have p0001 := (Nominal.classEqRefl (syn_cdm A))
  have p0002 :=
    @g_sseqtr4i (syn_cima (syn_ccnv A) B) (syn_crn (syn_ccnv A)) (syn_cdm A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_imasn (y : Var) (A : Class) (R : Class) (dv_A_y : y ∉ A.fv)
    (dv_R_y : y ∉ R.fv) :
    Nominal.NPrf (.classEq (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y)))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_A_y,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wbr A R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x R
      (syn_csn A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @g_breq1 (.cv x) A (.cv y) R
  have p0002 :=
    @g_rexsng (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) x A (syn_cvv)
      dv_cache_0006 dv_cache_0007 p0001
  have p0003 :=
    @g_abbidv (.classMem A (syn_cvv)) (syn_wrex x (syn_csn A) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr A R (.cv y)) y dv_cache_0008 p0002
  have p0004 :=
    @g_syl5eq (.classMem A (syn_cvv)) (syn_cima R (syn_csn A))
      (.cab y (syn_wrex x (syn_csn A) (syn_wbr (.cv x) R (.cv y))))
      (.cab y (syn_wbr A R (.cv y))) p0000 p0003
  have p0005 := @g_ima0 R
  have p0006 := @g_snprc A
  have p0007 :=
    @g_biimpi (.neg (.classMem A (syn_cvv))) (.classEq (syn_csn A) (syn_c0)) p0006
  have p0008 := @g_imaeq2d (.neg (.classMem A (syn_cvv))) (syn_csn A) (syn_c0) R p0007
  have p0009 := @g_brex A (.cv y) R
  have p0010 :=
    @g_simpld (syn_wbr A R (.cv y)) (.classMem A (syn_cvv)) (.classMem (.cv y) (syn_cvv))
      p0009
  have p0011 :=
    @g_exlimiv (syn_wbr A R (.cv y)) (.classMem A (syn_cvv)) y dv_cache_0008 p0010
  have p0012 := @g_con3i (syn_wex y (syn_wbr A R (.cv y))) (.classMem A (syn_cvv)) p0011
  have p0013 := @g_abn0 (syn_wbr A R (.cv y)) y
  have p0014 := (Nominal.biimpRefl (syn_wne (.cab y (syn_wbr A R (.cv y))) (syn_c0)))
  have p0015 :=
    @g_bitr3i (syn_wex y (syn_wbr A R (.cv y)))
      (syn_wne (.cab y (syn_wbr A R (.cv y))) (syn_c0))
      (.neg (.classEq (.cab y (syn_wbr A R (.cv y))) (syn_c0))) p0013 p0014
  have p0016 :=
    @g_con2bii (syn_wex y (syn_wbr A R (.cv y)))
      (.classEq (.cab y (syn_wbr A R (.cv y))) (syn_c0)) p0015
  have p0017 :=
    @g_sylibr (.neg (.classMem A (syn_cvv))) (.neg (syn_wex y (syn_wbr A R (.cv y))))
      (.classEq (.cab y (syn_wbr A R (.cv y))) (syn_c0)) p0012 p0016
  have p0018 :=
    @g_n_3eqtr4a (.neg (.classMem A (syn_cvv))) (syn_cima R (syn_c0)) (syn_c0)
      (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y))) p0005 p0008 p0017
  have p0019 :=
    @g_pm2_61i (.classMem A (syn_cvv))
      (.classEq (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y)))) p0004 p0018
  exact p0019

@[expose]
noncomputable def g_elimasn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_cima A (syn_csn B))) (.classMem (syn_cop B C) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : x ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wbr B A C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have p0000 := @g_elex C (syn_cima A (syn_csn B))
  have p0001 := (Nominal.biimpRefl (syn_wbr B A C))
  have p0002 := @g_brex B C A
  have p0003 :=
    @g_simprd (syn_wbr B A C) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002
  have p0004 :=
    @g_sylbir (.classMem (syn_cop B C) A) (syn_wbr B A C) (.classMem C (syn_cvv)) p0001
      p0003
  have p0005 := @g_breq2 (.cv x) C B A
  have p0006 :=
    @g_elabg (syn_wbr B A (.cv x)) (syn_wbr B A C) x C (syn_cvv) dv_cache_0001
      dv_cache_0002 p0005
  have p0007 := @g_imasn x B A dv_cache_0003 dv_cache_0004
  have p0008 := @g_eleq2i (syn_cima A (syn_csn B)) (.cab x (syn_wbr B A (.cv x))) C p0007
  have p0009 := @g_bicomi (syn_wbr B A C) (.classMem (syn_cop B C) A) p0001
  have p0010 :=
    @g_n_3bitr4g (.classMem C (syn_cvv)) (.classMem C (.cab x (syn_wbr B A (.cv x))))
      (syn_wbr B A C) (.classMem C (syn_cima A (syn_csn B))) (.classMem (syn_cop B C) A)
      p0006 p0008 p0009
  have p0011 :=
    @g_pm5_21nii (.classMem C (syn_cima A (syn_csn B))) (.classMem C (syn_cvv))
      (.classMem (syn_cop B C) A) p0000 p0004 p0010
  exact p0011

@[expose]
noncomputable def g_eliniseg (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_cima (syn_ccnv A) (syn_csn B))) (syn_wbr C A B)) :=
  by
  have p0000 := @g_elimasn (syn_ccnv A) B C
  have p0001 := (Nominal.biimpRefl (syn_wbr B (syn_ccnv A) C))
  have p0002 := @g_brcnv B C A
  have p0003 :=
    @g_n_3bitr2i (.classMem C (syn_cima (syn_ccnv A) (syn_csn B)))
      (.classMem (syn_cop B C) (syn_ccnv A)) (syn_wbr B (syn_ccnv A) C) (syn_wbr C A B)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_iniseg (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.classEq (syn_cima (syn_ccnv A) (syn_csn B)) (.cab x (syn_wbr (.cv x) A B))) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccnv A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, dv_A_x,
          not_false_eq_true])
  have p0000 := @g_imasn x B (syn_ccnv A) dv_cache_0001 dv_cache_0002
  have p0001 := @g_brcnv B (.cv x) A
  have p0002 := @g_abbii (syn_wbr B (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A B) x p0001
  have p0003 :=
    @g_eqtri (syn_cima (syn_ccnv A) (syn_csn B)) (.cab x (syn_wbr B (syn_ccnv A) (.cv x)))
      (.cab x (syn_wbr (.cv x) A B)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_imass2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cima C A) (syn_cima C B))) :=
  by
  have p0000 := @g_ssres2 A B C
  have p0001 := @g_rnss (syn_cres C A) (syn_cres C B)
  have p0002 :=
    @g_syl (syn_wss A B) (syn_wss (syn_cres C A) (syn_cres C B))
      (syn_wss (syn_crn (syn_cres C A)) (syn_crn (syn_cres C B))) p0000 p0001
  have p0003 := @g_dfima3 C A
  have p0004 := @g_dfima3 C B
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_crn (syn_cres C A)) (syn_crn (syn_cres C B))
      (syn_cima C A) (syn_cima C B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_ndmima (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A (syn_cdm B))) (.classEq (syn_cima B (syn_csn A)) (syn_c0))) :=
  by
  have p0000 := @g_dfima3 B (syn_csn A)
  have p0001 := @g_dmres B (syn_csn A)
  have p0002 := @g_incom (syn_csn A) (syn_cdm B)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_cres B (syn_csn A))) (syn_cin (syn_csn A) (syn_cdm B))
      (syn_cin (syn_cdm B) (syn_csn A)) p0001 p0002
  have p0004 := @g_disjsn (syn_cdm B) A
  have p0005 :=
    @g_biimpri (.classEq (syn_cin (syn_cdm B) (syn_csn A)) (syn_c0))
      (.neg (.classMem A (syn_cdm B))) p0004
  have p0006 :=
    @g_syl5eq (.neg (.classMem A (syn_cdm B))) (syn_cdm (syn_cres B (syn_csn A)))
      (syn_cin (syn_cdm B) (syn_csn A)) (syn_c0) p0003 p0005
  have p0007 := @g_dm0rn0 (syn_cres B (syn_csn A))
  have p0008 :=
    @g_sylib (.neg (.classMem A (syn_cdm B)))
      (.classEq (syn_cdm (syn_cres B (syn_csn A))) (syn_c0))
      (.classEq (syn_crn (syn_cres B (syn_csn A))) (syn_c0)) p0006 p0007
  have p0009 :=
    @g_syl5eq (.neg (.classMem A (syn_cdm B))) (syn_cima B (syn_csn A))
      (syn_crn (syn_cres B (syn_csn A))) (syn_c0) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_cnvopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_copab x y ph)) (syn_copab y x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
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
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0004 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0005 : z ∉ ((syn_ccnv (syn_copab x y ph))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_ccnv (syn_copab x y ph))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_ph, fresh_w_ne_x, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_copab y x ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_z_not_ph,
          fresh_z_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_copab y x ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_w_not_ph,
          fresh_w_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 := @g_opelopabsb ph x y (.cv w) (.cv z) dv_cache_0001 dv_cache_0002
  have p0001 := @g_sbccom ph x y (.cv w) (.cv z) dv_cache_0003 dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_bitri (.classMem (syn_cop (.cv w) (.cv z)) (syn_copab x y ph))
      (syn_wsbc (.cv w) x (syn_wsbc (.cv z) y ph))
      (syn_wsbc (.cv z) y (syn_wsbc (.cv w) x ph)) p0000 p0001
  have p0003 := @g_opelcnv (.cv z) (.cv w) (syn_copab x y ph)
  have p0004 := @g_opelopabsb ph y x (.cv z) (.cv w) dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv w) (.cv z)) (syn_copab x y ph))
      (syn_wsbc (.cv z) y (syn_wsbc (.cv w) x ph))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_ccnv (syn_copab x y ph)))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab y x ph)) p0002 p0003 p0004
  have p0006 :=
    @g_eqrelriv z w (syn_ccnv (syn_copab x y ph)) (syn_copab y x ph) dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0005
  exact p0006

@[expose]
noncomputable def g_cnv0 : Nominal.NPrf (.classEq (syn_ccnv (syn_c0)) (syn_c0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_c0))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_c0))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_noel (syn_cop (.cv y) (.cv x))
  have p0001 := @g_opelcnv (.cv x) (.cv y) (syn_c0)
  have p0002 :=
    @g_mtbir (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_c0)))
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_c0)) p0000 p0001
  have p0003 := @g_noel (syn_cop (.cv x) (.cv y))
  have p0004 :=
    @g_n_2false (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_c0)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)) p0002 p0003
  have p0005 :=
    @g_eqrelriv x y (syn_ccnv (syn_c0)) (syn_c0) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0004
  exact p0005

@[expose]
noncomputable def g_cnvi : Nominal.NPrf (.classEq (syn_ccnv (syn_cid)) (syn_cid)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_cid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cid)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_vex x
  have p0001 := @g_ideq (.cv y) (.cv x) p0000
  have p0002 := @g_equcom y x
  have p0003_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0002
  have p0003 :=
    @g_bitri (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x))
      (.classEq (.cv x) (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @g_opabbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv x) (.cv y)) x y p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y (syn_cid)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_id x y dv_cache_0003
  have p0007_e02_recanon :
    Nominal.NPrf (.classEq (syn_cid) (syn_copab x y (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cid syn_copab syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0006
  have p0007 :=
    @g_n_3eqtr4i (syn_copab x y (syn_wbr (.cv y) (syn_cid) (.cv x)))
      (syn_copab x y (.classEq (.cv x) (.cv y))) (syn_ccnv (syn_cid)) (syn_cid) p0004
      p0005 p0007_e02_recanon
  exact p0007

@[expose]
noncomputable def g_cnvun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cun A B)) (syn_cun (syn_ccnv A) (syn_ccnv B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0006 : x ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_unopab (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x)) x y
  have p0001 := @g_brun (.cv y) (.cv x) A B
  have p0002 :=
    @g_opabbii (syn_wbr (.cv y) (syn_cun A B) (.cv x))
      (syn_wo (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x))) x y p0001
  have p0003 :=
    @g_eqtr4i
      (syn_cun (syn_copab x y (syn_wbr (.cv y) A (.cv x)))
        (syn_copab x y (syn_wbr (.cv y) B (.cv x))))
      (syn_copab x y (syn_wo (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x))))
      (syn_copab x y (syn_wbr (.cv y) (syn_cun A B) (.cv x))) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y B
      dv_cache_0004 dv_cache_0005 dv_cache_0003
  have p0006 :=
    @g_uneq12i (syn_ccnv A) (syn_copab x y (syn_wbr (.cv y) A (.cv x))) (syn_ccnv B)
      (syn_copab x y (syn_wbr (.cv y) B (.cv x))) p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y
      (syn_cun A B) dv_cache_0006 dv_cache_0007 dv_cache_0003
  have p0008 :=
    @g_n_3eqtr4ri
      (syn_cun (syn_copab x y (syn_wbr (.cv y) A (.cv x)))
        (syn_copab x y (syn_wbr (.cv y) B (.cv x))))
      (syn_copab x y (syn_wbr (.cv y) (syn_cun A B) (.cv x)))
      (syn_cun (syn_ccnv A) (syn_ccnv B)) (syn_ccnv (syn_cun A B)) p0003 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_cnvdif (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cdif A B)) (syn_cdif (syn_ccnv A) (syn_ccnv B))) :=
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
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_cdif A B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_cdif A B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdif (syn_ccnv A) (syn_ccnv B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cdif (syn_ccnv A) (syn_ccnv B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_eldif (syn_cop (.cv y) (.cv x)) A B
  have p0001 := @g_opelcnv (.cv x) (.cv y) A
  have p0002 := @g_opelcnv (.cv x) (.cv y) B
  have p0003 :=
    @g_notbii (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B))
      (.classMem (syn_cop (.cv y) (.cv x)) B) p0002
  have p0004 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A))
      (.classMem (syn_cop (.cv y) (.cv x)) A)
      (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B)))
      (.neg (.classMem (syn_cop (.cv y) (.cv x)) B)) p0001 p0003
  have p0005 :=
    @g_bitr4i (.classMem (syn_cop (.cv y) (.cv x)) (syn_cdif A B))
      (syn_wa (.classMem (syn_cop (.cv y) (.cv x)) A)
        (.neg (.classMem (syn_cop (.cv y) (.cv x)) B)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A))
        (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B))))
      p0000 p0004
  have p0006 := @g_opelcnv (.cv x) (.cv y) (syn_cdif A B)
  have p0007 := @g_eldif (syn_cop (.cv x) (.cv y)) (syn_ccnv A) (syn_ccnv B)
  have p0008 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv y) (.cv x)) (syn_cdif A B))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A))
        (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B))))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_cdif A B)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cdif (syn_ccnv A) (syn_ccnv B))) p0005
      p0006 p0007
  have p0009 :=
    @g_eqrelriv x y (syn_ccnv (syn_cdif A B)) (syn_cdif (syn_ccnv A) (syn_ccnv B))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008
  exact p0009

@[expose]
noncomputable def g_cnvin (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cin A B)) (syn_cin (syn_ccnv A) (syn_ccnv B))) :=
  by
  have p0000 := @g_cnvdif A (syn_cdif A B)
  have p0001 := @g_cnvdif A B
  have p0002 :=
    @g_difeq2i (syn_ccnv (syn_cdif A B)) (syn_cdif (syn_ccnv A) (syn_ccnv B)) (syn_ccnv A)
      p0001
  have p0003 :=
    @g_eqtri (syn_ccnv (syn_cdif A (syn_cdif A B)))
      (syn_cdif (syn_ccnv A) (syn_ccnv (syn_cdif A B)))
      (syn_cdif (syn_ccnv A) (syn_cdif (syn_ccnv A) (syn_ccnv B))) p0000 p0002
  have p0004 := @g_dfin4 A B
  have p0005 := @g_cnveqi (syn_cin A B) (syn_cdif A (syn_cdif A B)) p0004
  have p0006 := @g_dfin4 (syn_ccnv A) (syn_ccnv B)
  have p0007 :=
    @g_n_3eqtr4i (syn_ccnv (syn_cdif A (syn_cdif A B)))
      (syn_cdif (syn_ccnv A) (syn_cdif (syn_ccnv A) (syn_ccnv B)))
      (syn_ccnv (syn_cin A B)) (syn_cin (syn_ccnv A) (syn_ccnv B)) p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_rnun (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_crn (syn_cun A B)) (syn_cun (syn_crn A) (syn_crn B))) :=
  by
  have p0000 := @g_cnvun A B
  have p0001 :=
    @g_dmeqi (syn_ccnv (syn_cun A B)) (syn_cun (syn_ccnv A) (syn_ccnv B)) p0000
  have p0002 := @g_dmun (syn_ccnv A) (syn_ccnv B)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_ccnv (syn_cun A B)))
      (syn_cdm (syn_cun (syn_ccnv A) (syn_ccnv B)))
      (syn_cun (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) p0001 p0002
  have p0004 := @g_dfrn4 (syn_cun A B)
  have p0005 := @g_dfrn4 A
  have p0006 := @g_dfrn4 B
  have p0007 :=
    @g_uneq12i (syn_crn A) (syn_cdm (syn_ccnv A)) (syn_crn B) (syn_cdm (syn_ccnv B)) p0005
      p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cdm (syn_ccnv (syn_cun A B)))
      (syn_cun (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) (syn_crn (syn_cun A B))
      (syn_cun (syn_crn A) (syn_crn B)) p0003 p0004 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_rnuni (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_crn (syn_cuni A)) (syn_ciun x A (syn_crn (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : x ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_y_not_A,
          not_false_eq_true])
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
  have dv_cache_0008 : z ∉ ((syn_crn (syn_cuni A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_ciun x A (syn_crn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_eluni x (syn_cop (.cv y) (.cv z)) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))
      (syn_wex x (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      y p0000
  have p0002 :=
    @g_excom (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))
      y x
  have p0003 := @g_elrn2 y (.cv z) (.cv x) dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_anbi1i (.classMem (.cv z) (syn_crn (.cv x)))
      (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)
      p0003
  have p0005 := @g_ancom (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))
  have p0006 :=
    @g_n_19_41v (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A) y
      dv_cache_0005
  have p0007 :=
    @g_n_3bitr4ri (syn_wa (.classMem (.cv z) (syn_crn (.cv x))) (.classMem (.cv x) A))
      (syn_wa (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x))))
      (syn_wex y (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      p0004 p0005 p0006
  have p0008 :=
    @g_exbii
      (syn_wex y (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))) x p0007
  have p0009 :=
    @g_n_3bitri (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)))
      (syn_wex y (syn_wex x
          (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (syn_wex x (syn_wex y
          (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))))
      p0001 p0002 p0008
  have p0010 := (Nominal.biimpRefl (syn_wrex x A (.classMem (.cv z) (syn_crn (.cv x)))))
  have p0011 :=
    @g_bitr4i (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv z) (syn_crn (.cv x)))))
      (syn_wrex x A (.classMem (.cv z) (syn_crn (.cv x)))) p0009 p0010
  have p0012 := @g_elrn2 y (.cv z) (syn_cuni A) dv_cache_0003 dv_cache_0006
  have p0013 := @g_eliun x (.cv z) A (syn_crn (.cv x)) dv_cache_0007
  have p0014 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)))
      (syn_wrex x A (.classMem (.cv z) (syn_crn (.cv x))))
      (.classMem (.cv z) (syn_crn (syn_cuni A)))
      (.classMem (.cv z) (syn_ciun x A (syn_crn (.cv x)))) p0011 p0012 p0013
  have p0015 :=
    @g_eqriv z (syn_crn (syn_cuni A)) (syn_ciun x A (syn_crn (.cv x))) dv_cache_0008
      dv_cache_0009 p0014
  exact p0015

@[expose]
noncomputable def g_imaundi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cima A (syn_cun B C)) (syn_cun (syn_cima A B) (syn_cima A C))) :=
  by
  have p0000 := @g_resundi A B C
  have p0001 :=
    @g_rneqi (syn_cres A (syn_cun B C)) (syn_cun (syn_cres A B) (syn_cres A C)) p0000
  have p0002 := @g_rnun (syn_cres A B) (syn_cres A C)
  have p0003 :=
    @g_eqtri (syn_crn (syn_cres A (syn_cun B C)))
      (syn_crn (syn_cun (syn_cres A B) (syn_cres A C)))
      (syn_cun (syn_crn (syn_cres A B)) (syn_crn (syn_cres A C))) p0001 p0002
  have p0004 := @g_dfima3 A (syn_cun B C)
  have p0005 := @g_dfima3 A B
  have p0006 := @g_dfima3 A C
  have p0007 :=
    @g_uneq12i (syn_cima A B) (syn_crn (syn_cres A B)) (syn_cima A C)
      (syn_crn (syn_cres A C)) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_crn (syn_cres A (syn_cun B C)))
      (syn_cun (syn_crn (syn_cres A B)) (syn_crn (syn_cres A C)))
      (syn_cima A (syn_cun B C)) (syn_cun (syn_cima A B) (syn_cima A C)) p0003 p0004 p0007
  exact p0008

@[expose]
noncomputable def g_imaundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cima (syn_cun A B) C) (syn_cun (syn_cima A C) (syn_cima B C))) :=
  by
  have p0000 := @g_dfima3 (syn_cun A B) C
  have p0001 := @g_resundir A B C
  have p0002 :=
    @g_rneqi (syn_cres (syn_cun A B) C) (syn_cun (syn_cres A C) (syn_cres B C)) p0001
  have p0003 := @g_rnun (syn_cres A C) (syn_cres B C)
  have p0004 :=
    @g_n_3eqtri (syn_cima (syn_cun A B) C) (syn_crn (syn_cres (syn_cun A B) C))
      (syn_crn (syn_cun (syn_cres A C) (syn_cres B C)))
      (syn_cun (syn_crn (syn_cres A C)) (syn_crn (syn_cres B C))) p0000 p0002 p0003
  have p0005 := @g_dfima3 A C
  have p0006 := @g_dfima3 B C
  have p0007 :=
    @g_uneq12i (syn_cima A C) (syn_crn (syn_cres A C)) (syn_cima B C)
      (syn_crn (syn_cres B C)) p0005 p0006
  have p0008 :=
    @g_eqtr4i (syn_cima (syn_cun A B) C)
      (syn_cun (syn_crn (syn_cres A C)) (syn_crn (syn_cres B C)))
      (syn_cun (syn_cima A C) (syn_cima B C)) p0004 p0007
  exact p0008

@[expose]
noncomputable def g_cnvxp (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cxp A B)) (syn_cxp B A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ≠ x := by exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_cnvopab (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)) y x dv_cache_0001
  have p0001 := @g_ancom (.classMem (.cv y) A) (.classMem (.cv x) B)
  have p0002 :=
    @g_opabbii (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A)) x y p0001
  have p0003 :=
    @g_eqtri
      (syn_ccnv (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))))
      (syn_copab x y (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A))) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp y x A B
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
  have p0005 :=
    @g_cnveqi (syn_cxp A B)
      (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))) p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B A
      dv_cache_0005 dv_cache_0004 dv_cache_0003 dv_cache_0002 dv_cache_0006
  have p0007 :=
    @g_n_3eqtr4i
      (syn_ccnv (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))))
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A)))
      (syn_ccnv (syn_cxp A B)) (syn_cxp B A) p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_xp0 (A : Class) :
    Nominal.NPrf (.classEq (syn_cxp A (syn_c0)) (syn_c0)) :=
  by
  have p0000 := @g_xp0r A
  have p0001 := @g_cnveqi (syn_cxp (syn_c0) A) (syn_c0) p0000
  have p0002 := @g_cnvxp (syn_c0) A
  have p0003 := @g_cnv0
  have p0004 :=
    @g_n_3eqtr3i (syn_ccnv (syn_cxp (syn_c0) A)) (syn_ccnv (syn_c0)) (syn_cxp A (syn_c0))
      (syn_c0) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_xpdisj2 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (.classEq (syn_cin A B) (syn_c0))
        (.classEq (syn_cin (syn_cxp C A) (syn_cxp D B)) (syn_c0))) :=
  by
  have p0000 := @g_inxp C A D B
  have p0001 := @g_xpeq2 (syn_cin A B) (syn_c0) (syn_cin C D)
  have p0002 := @g_xp0 (syn_cin C D)
  have p0003 :=
    @g_syl6eq (.classEq (syn_cin A B) (syn_c0)) (syn_cxp (syn_cin C D) (syn_cin A B))
      (syn_cxp (syn_cin C D) (syn_c0)) (syn_c0) p0001 p0002
  have p0004 :=
    @g_syl5eq (.classEq (syn_cin A B) (syn_c0)) (syn_cin (syn_cxp C A) (syn_cxp D B))
      (syn_cxp (syn_cin C D) (syn_cin A B)) (syn_c0) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_dmxpss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cdm (syn_cxp A B)) A) :=
  by
  have p0000 := @g_n_0ss A
  have p0001 := @g_xpeq2 B (syn_c0) A
  have p0002 := @g_xp0 A
  have p0003 :=
    @g_syl6eq (.classEq B (syn_c0)) (syn_cxp A B) (syn_cxp A (syn_c0)) (syn_c0) p0001
      p0002
  have p0004 := @g_dmeqd (.classEq B (syn_c0)) (syn_cxp A B) (syn_c0) p0003
  have p0005 := @g_dm0
  have p0006 :=
    @g_syl6eq (.classEq B (syn_c0)) (syn_cdm (syn_cxp A B)) (syn_cdm (syn_c0)) (syn_c0)
      p0004 p0005
  have p0007 := @g_sseq1d (.classEq B (syn_c0)) (syn_cdm (syn_cxp A B)) (syn_c0) A p0006
  have p0008 :=
    @g_mpbiri (.classEq B (syn_c0)) (syn_wss (syn_cdm (syn_cxp A B)) A)
      (syn_wss (syn_c0) A) p0000 p0007
  have p0009 := @g_dmxp A B
  have p0010 := @g_eqimss (syn_cdm (syn_cxp A B)) A
  have p0011 :=
    @g_syl (syn_wne B (syn_c0)) (.classEq (syn_cdm (syn_cxp A B)) A)
      (syn_wss (syn_cdm (syn_cxp A B)) A) p0009 p0010
  have p0012 := @g_pm2_61ine (syn_wss (syn_cdm (syn_cxp A B)) A) B (syn_c0) p0008 p0011
  exact p0012

@[expose]
noncomputable def g_rnxpss (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_crn (syn_cxp A B)) B) :=
  by
  have p0000 := @g_dfrn4 (syn_cxp A B)
  have p0001 := @g_cnvxp A B
  have p0002 := @g_dmeqi (syn_ccnv (syn_cxp A B)) (syn_cxp B A) p0001
  have p0003 :=
    @g_eqtri (syn_crn (syn_cxp A B)) (syn_cdm (syn_ccnv (syn_cxp A B)))
      (syn_cdm (syn_cxp B A)) p0000 p0002
  have p0004 := @g_dmxpss B A
  have p0005 := @g_eqsstri (syn_crn (syn_cxp A B)) (syn_cdm (syn_cxp B A)) B p0003 p0004
  exact p0005

@[expose]
noncomputable def g_cnvcnv (R : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_ccnv R)) R) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_ccnv R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_ccnv R))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_brcnv (.cv x) (.cv y) (syn_ccnv R)
  have p0001 := @g_brcnv (.cv y) (.cv x) R
  have p0002 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_ccnv R)) (.cv y))
      (syn_wbr (.cv y) (syn_ccnv R) (.cv x)) (syn_wbr (.cv x) R (.cv y)) p0000 p0001
  have p0003 :=
    @g_eqbrriv x y (syn_ccnv (syn_ccnv R)) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0002
  exact p0003

@[expose]
noncomputable def g_cnveqb (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B))) :=
  by
  have p0000 := @g_cnveq A B
  have p0001 := @g_cnveq (syn_ccnv A) (syn_ccnv B)
  have p0002 := @g_cnvcnv A
  have p0003 := @g_cnvcnv B
  have p0004 :=
    @g_n_3eqtr3g (.classEq (syn_ccnv A) (syn_ccnv B)) (syn_ccnv (syn_ccnv A))
      (syn_ccnv (syn_ccnv B)) A B p0001 p0002 p0003
  have p0005 := @g_impbii (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_dmsnopg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem B V) (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_csn (syn_cop A (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cdm (syn_csn (syn_cop A (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0009 :
    y ∉ ((Wff.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_opeq2 (.cv y) B A
  have p0001 := @g_sneqd (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) p0000
  have p0002 :=
    @g_dmeqd (.classEq (.cv y) B) (syn_csn (syn_cop A (.cv y))) (syn_csn (syn_cop A B))
      p0001
  have p0003 :=
    @g_eqeq1d (.classEq (.cv y) B) (syn_cdm (syn_csn (syn_cop A (.cv y))))
      (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A) p0002
  have p0004 :=
    (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z)))
  have p0005 := @g_vex x
  have p0006 := @g_vex z
  have p0007 := @g_opex (.cv x) (.cv z) p0005 p0006
  have p0008 := @g_elsnc (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y)) p0007
  have p0009 := @g_opth (.cv x) (.cv z) A (.cv y)
  have p0010 := @g_ancom (.classEq (.cv x) A) (.objEq z y)
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y)))
        (syn_wa (.classEq (.cv x) A) (.objEq z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0011 :=
    @g_bitri (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y)))
      (syn_wa (.classEq (.cv x) A) (.objEq z y))
      (syn_wa (.objEq z y) (.classEq (.cv x) A)) p0011_e00_recanon p0010
  have p0012 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z))
      (.classMem (syn_cop (.cv x) (.cv z)) (syn_csn (syn_cop A (.cv y))))
      (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop A (.cv y)))
      (syn_wa (.objEq z y) (.classEq (.cv x) A)) p0004 p0008 p0011
  have p0013 :=
    @g_exbii (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z))
      (syn_wa (.objEq z y) (.classEq (.cv x) A)) z p0012
  have p0014 := @g_vex y
  have p0015 := @g_biidd (.objEq z y) (.classEq (.cv x) A)
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y)) (syn_wb (.classEq (.cv x) A) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @g_ceqsexv (.classEq (.cv x) A) (.classEq (.cv x) A) z (.cv y) dv_cache_0001
      dv_cache_0002 p0014 p0016_e01_recanon
  have p0017_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex z (syn_wa (.objEq z y) (.classEq (.cv x) A))) (.classEq (.cv x) A)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_bitri (syn_wex z (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z)))
      (syn_wex z (syn_wa (.objEq z y) (.classEq (.cv x) A))) (.classEq (.cv x) A) p0013
      p0017_e01_recanon
  have p0018 :=
    @g_eldm z (.cv x) (syn_csn (syn_cop A (.cv y))) dv_cache_0003 dv_cache_0004
  have p0019 := @g_elsn x A dv_cache_0005
  have p0020 :=
    @g_n_3bitr4i (syn_wex z (syn_wbr (.cv x) (syn_csn (syn_cop A (.cv y))) (.cv z)))
      (.classEq (.cv x) A) (.classMem (.cv x) (syn_cdm (syn_csn (syn_cop A (.cv y)))))
      (.classMem (.cv x) (syn_csn A)) p0017 p0018 p0019
  have p0021 :=
    @g_eqriv x (syn_cdm (syn_csn (syn_cop A (.cv y)))) (syn_csn A) dv_cache_0006
      dv_cache_0007 p0020
  have p0022 :=
    @g_vtoclg (.classEq (syn_cdm (syn_csn (syn_cop A (.cv y)))) (syn_csn A))
      (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A)) y B V dv_cache_0008
      dv_cache_0009 p0003 p0021
  exact p0022

@[expose]
noncomputable def g_dmsnop (A : Class) (B : Class)
    (hyp_dmsnop_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A)) :=
  by
  have p0000 := @g_dmsnopg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_dmsnop_1 p0000
  exact p0001

@[expose]
noncomputable def g_cnvsn (A : Class) (B : Class)
    (_hyp_cnvsn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (_hyp_cnvsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn (syn_cop B A))) :=
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
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_csn (syn_cop A B)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_csn (syn_cop A B)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_csn (syn_cop B A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_csn (syn_cop B A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_vex y
  have p0001 := @g_vex x
  have p0002 := @g_opex (.cv y) (.cv x) p0000 p0001
  have p0003 := @g_elsnc (syn_cop (.cv y) (.cv x)) (syn_cop A B) p0002
  have p0004 := @g_ancom (.classEq (.cv y) A) (.classEq (.cv x) B)
  have p0005 := @g_opth (.cv y) (.cv x) A B
  have p0006 := @g_opth (.cv x) (.cv y) B A
  have p0007 :=
    @g_n_3bitr4i (syn_wa (.classEq (.cv y) A) (.classEq (.cv x) B))
      (syn_wa (.classEq (.cv x) B) (.classEq (.cv y) A))
      (.classEq (syn_cop (.cv y) (.cv x)) (syn_cop A B))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B A)) p0004 p0005 p0006
  have p0008 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv x)) (syn_csn (syn_cop A B)))
      (.classEq (syn_cop (.cv y) (.cv x)) (syn_cop A B))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B A)) p0003 p0007
  have p0009 := @g_opelcnv (.cv x) (.cv y) (syn_csn (syn_cop A B))
  have p0010 := @g_opex (.cv x) (.cv y) p0001 p0000
  have p0011 := @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop B A) p0010
  have p0012 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv y) (.cv x)) (syn_csn (syn_cop A B)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B A))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_csn (syn_cop A B))))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop B A))) p0008 p0009 p0011
  have p0013 :=
    @g_eqrelriv x y (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn (syn_cop B A))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0012
  exact p0013

@[expose]
noncomputable def g_rnsnop (A : Class) (B : Class)
    (hyp_rnsnop_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_crn (syn_csn (syn_cop A B))) (syn_csn B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_csn (syn_cop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_crn (syn_csn (syn_cop A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_csn B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_B,
          not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)))
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_opex (.cv x) (.cv y) p0001 p0002
  have p0004 := @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop A B) p0003
  have p0005 := @g_opth (.cv x) (.cv y) A B
  have p0006 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0004 p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B)))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0006
  have p0008 :=
    @g_exbii (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) x p0007
  have p0009 := @g_biidd (.classEq (.cv x) A) (.classEq (.cv y) B)
  have p0010 :=
    @g_ceqsexv (.classEq (.cv y) B) (.classEq (.cv y) B) x A dv_cache_0001 dv_cache_0002
      hyp_rnsnop_1 p0009
  have p0011 :=
    @g_bitri (syn_wex x (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))) (.classEq (.cv y) B)
      p0008 p0010
  have p0012 := @g_elrn x (.cv y) (syn_csn (syn_cop A B)) dv_cache_0003 dv_cache_0004
  have p0013 := @g_elsnc (.cv y) B p0002
  have p0014 :=
    @g_n_3bitr4i (syn_wex x (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)))
      (.classEq (.cv y) B) (.classMem (.cv y) (syn_crn (syn_csn (syn_cop A B))))
      (.classMem (.cv y) (syn_csn B)) p0011 p0012 p0013
  have p0015 :=
    @g_eqriv y (syn_crn (syn_csn (syn_cop A B))) (syn_csn B) dv_cache_0005 dv_cache_0006
      p0014
  exact p0015

@[expose]
noncomputable def g_cnvresima (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.classEq (syn_cima (syn_ccnv (syn_cres F A)) B) (syn_cin (syn_cima (syn_ccnv F) B) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let t : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_t_ne_s : t ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_t : s ≠ t := Ne.symm fresh_t_ne_s
  have dv_cache_0001 : s ∉ ((Class.cv t)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_t, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((syn_ccnv (syn_cres F A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_s_not_F, fresh_s_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : s ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_B, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((Wff.classMem (.cv t) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_t, fresh_s_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_ccnv F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_s_not_F,
          not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_cima (syn_ccnv (syn_cres F A)) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_t_not_F, fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_cin (syn_cima (syn_ccnv F) B) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_t_not_F, fresh_t_not_B, fresh_t_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @g_elima3 s (.cv t) (syn_ccnv (syn_cres F A)) B dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 :=
    @g_anass (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))
      (.classMem (.cv t) A)
  have p0002 := @g_opelres (.cv t) (.cv s) F A
  have p0003 := @g_opelcnv (.cv s) (.cv t) (syn_cres F A)
  have p0004 := @g_opelcnv (.cv s) (.cv t) F
  have p0005 :=
    @g_anbi1i (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))
      (.classMem (syn_cop (.cv t) (.cv s)) F) (.classMem (.cv t) A) p0004
  have p0006 :=
    @g_n_3bitr4ri (.classMem (syn_cop (.cv t) (.cv s)) (syn_cres F A))
      (syn_wa (.classMem (syn_cop (.cv t) (.cv s)) F) (.classMem (.cv t) A))
      (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A)))
      (syn_wa (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A))
      p0002 p0003 p0005
  have p0007 :=
    @g_anbi2i
      (syn_wa (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A))
      (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A)))
      (.classMem (.cv s) B) p0006
  have p0008 :=
    @g_bitr2i
      (syn_wa (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))
        (.classMem (.cv t) A))
      (syn_wa (.classMem (.cv s) B)
        (syn_wa (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)) (.classMem (.cv t) A)))
      (syn_wa (.classMem (.cv s) B)
        (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A))))
      p0001 p0007
  have p0009 :=
    @g_exbii
      (syn_wa (.classMem (.cv s) B)
        (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A))))
      (syn_wa (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))
        (.classMem (.cv t) A))
      s p0008
  have p0010 :=
    @g_n_19_41v
      (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))
      (.classMem (.cv t) A) s dv_cache_0004
  have p0011 :=
    @g_bitri
      (syn_wex s (syn_wa (.classMem (.cv s) B)
          (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A)))))
      (syn_wex s (syn_wa (syn_wa (.classMem (.cv s) B)
            (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))) (.classMem (.cv t) A)))
      (syn_wa (syn_wex s (syn_wa (.classMem (.cv s) B)
            (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A))
      p0009 p0010
  have p0012 := @g_elin (.cv t) (syn_cima (syn_ccnv F) B) A
  have p0013 :=
    @g_elima3 s (.cv t) (syn_ccnv F) B dv_cache_0001 dv_cache_0005 dv_cache_0003
  have p0014 :=
    @g_anbi1i (.classMem (.cv t) (syn_cima (syn_ccnv F) B))
      (syn_wex s
        (syn_wa (.classMem (.cv s) B) (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F))))
      (.classMem (.cv t) A) p0013
  have p0015 :=
    @g_bitr2i (.classMem (.cv t) (syn_cin (syn_cima (syn_ccnv F) B) A))
      (syn_wa (.classMem (.cv t) (syn_cima (syn_ccnv F) B)) (.classMem (.cv t) A))
      (syn_wa (syn_wex s (syn_wa (.classMem (.cv s) B)
            (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A))
      p0012 p0014
  have p0016 :=
    @g_n_3bitri (.classMem (.cv t) (syn_cima (syn_ccnv (syn_cres F A)) B))
      (syn_wex s (syn_wa (.classMem (.cv s) B)
          (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv (syn_cres F A)))))
      (syn_wa (syn_wex s (syn_wa (.classMem (.cv s) B)
            (.classMem (syn_cop (.cv s) (.cv t)) (syn_ccnv F)))) (.classMem (.cv t) A))
      (.classMem (.cv t) (syn_cin (syn_cima (syn_ccnv F) B) A)) p0000 p0011 p0015
  have p0017 :=
    @g_eqriv t (syn_cima (syn_ccnv (syn_cres F A)) B)
      (syn_cin (syn_cima (syn_ccnv F) B) A) dv_cache_0006 dv_cache_0007 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_resco (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cres (syn_ccom A B) C) (syn_ccom A (syn_cres B C))) :=
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
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Wff.classMem (.cv x) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_C, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cres B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, fresh_z_not_B, fresh_z_not_C, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cres (syn_ccom A B) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cres (syn_ccom A B) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_ccom A (syn_cres B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_ccom A (syn_cres B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_brco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_ccom A B) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_n_19_41v (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
      (.classMem (.cv x) C) z dv_cache_0005
  have p0003 :=
    @g_an32 (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)) (.classMem (.cv x) C)
  have p0004 := @g_brres (.cv x) (.cv z) B C
  have p0005 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_cres B C) (.cv z))
      (syn_wa (syn_wbr (.cv x) B (.cv z)) (.classMem (.cv x) C))
      (syn_wbr (.cv z) A (.cv y)) p0004
  have p0006 :=
    @g_bitr4i
      (syn_wa (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
        (.classMem (.cv x) C))
      (syn_wa (syn_wa (syn_wbr (.cv x) B (.cv z)) (.classMem (.cv x) C))
        (syn_wbr (.cv z) A (.cv y)))
      (syn_wa (syn_wbr (.cv x) (syn_cres B C) (.cv z)) (syn_wbr (.cv z) A (.cv y))) p0003
      p0005
  have p0007 :=
    @g_exbii
      (syn_wa (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
        (.classMem (.cv x) C))
      (syn_wa (syn_wbr (.cv x) (syn_cres B C) (.cv z)) (syn_wbr (.cv z) A (.cv y))) z
      p0006
  have p0008 :=
    @g_n_3bitr2i (syn_wa (syn_wbr (.cv x) (syn_ccom A B) (.cv y)) (.classMem (.cv x) C))
      (syn_wa (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))
        (.classMem (.cv x) C))
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
          (.classMem (.cv x) C)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_cres B C) (.cv z)) (syn_wbr (.cv z) A (.cv y))))
      p0001 p0002 p0007
  have p0009 := @g_brres (.cv x) (.cv y) (syn_ccom A B) C
  have p0010 :=
    @g_brco z (.cv x) (.cv y) A (syn_cres B C) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0006
  have p0011 :=
    @g_n_3bitr4i (syn_wa (syn_wbr (.cv x) (syn_ccom A B) (.cv y)) (.classMem (.cv x) C))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_cres B C) (.cv z)) (syn_wbr (.cv z) A (.cv y))))
      (syn_wbr (.cv x) (syn_cres (syn_ccom A B) C) (.cv y))
      (syn_wbr (.cv x) (syn_ccom A (syn_cres B C)) (.cv y)) p0008 p0009 p0010
  have p0012 :=
    @g_eqbrriv x y (syn_cres (syn_ccom A B) C) (syn_ccom A (syn_cres B C)) dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0011
  exact p0012

@[expose]
noncomputable def g_imaco (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cima (syn_ccom A B) C) (syn_cima A (syn_cima B C))) :=
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
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cima B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          Finset.mem_union, fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_wbr (.cv y) A (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_ccom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
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
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0010 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0011 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0012 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0013 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_cima (syn_ccom A B) C)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cima A (syn_cima B C))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false,
          not_false_eq_true])
  have p0000 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cima B C) (syn_wbr (.cv y) A (.cv x))))
  have p0001 :=
    @g_elima y (.cv x) A (syn_cima B C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_r19_41v (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x)) z C dv_cache_0004
  have p0003 :=
    @g_exbii
      (syn_wrex z C (syn_wa (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x))))
      (syn_wa (syn_wrex z C (syn_wbr (.cv z) B (.cv y))) (syn_wbr (.cv y) A (.cv x))) y
      p0002
  have p0004 :=
    @g_elima z (.cv x) (syn_ccom A B) C dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_brco y (.cv z) (.cv x) A B dv_cache_0008 dv_cache_0001 dv_cache_0002 dv_cache_0009
  have p0006 :=
    @g_rexbii (syn_wbr (.cv z) (syn_ccom A B) (.cv x))
      (syn_wex y (syn_wa (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x)))) z C
      p0005
  have p0007 :=
    @g_rexcom4 (syn_wa (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x))) z y C
      dv_cache_0010 dv_cache_0011
  have p0008 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cima (syn_ccom A B) C))
      (syn_wrex z C (syn_wbr (.cv z) (syn_ccom A B) (.cv x)))
      (syn_wrex z C
        (syn_wex y (syn_wa (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x)))))
      (syn_wex y
        (syn_wrex z C (syn_wa (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x)))))
      p0004 p0006 p0007
  have p0009 := @g_elima z (.cv y) B C dv_cache_0012 dv_cache_0013 dv_cache_0007
  have p0010 :=
    @g_anbi1i (.classMem (.cv y) (syn_cima B C))
      (syn_wrex z C (syn_wbr (.cv z) B (.cv y))) (syn_wbr (.cv y) A (.cv x)) p0009
  have p0011 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cima B C)) (syn_wbr (.cv y) A (.cv x)))
      (syn_wa (syn_wrex z C (syn_wbr (.cv z) B (.cv y))) (syn_wbr (.cv y) A (.cv x))) y
      p0010
  have p0012 :=
    @g_n_3bitr4i
      (syn_wex y
        (syn_wrex z C (syn_wa (syn_wbr (.cv z) B (.cv y)) (syn_wbr (.cv y) A (.cv x)))))
      (syn_wex y
        (syn_wa (syn_wrex z C (syn_wbr (.cv z) B (.cv y))) (syn_wbr (.cv y) A (.cv x))))
      (.classMem (.cv x) (syn_cima (syn_ccom A B) C))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cima B C)) (syn_wbr (.cv y) A (.cv x))))
      p0003 p0008 p0011
  have p0013 :=
    @g_n_3bitr4ri (syn_wrex y (syn_cima B C) (syn_wbr (.cv y) A (.cv x)))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cima B C)) (syn_wbr (.cv y) A (.cv x))))
      (.classMem (.cv x) (syn_cima A (syn_cima B C)))
      (.classMem (.cv x) (syn_cima (syn_ccom A B) C)) p0000 p0001 p0012
  have p0014 :=
    @g_eqriv x (syn_cima (syn_ccom A B) C) (syn_cima A (syn_cima B C)) dv_cache_0014
      dv_cache_0015 p0013
  exact p0014

@[expose]
noncomputable def g_co01 (A : Class) :
    Nominal.NPrf (.classEq (syn_ccom (syn_c0) A) (syn_c0)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ccom (syn_c0) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cproj1 (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cproj2 (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have p0000 := @g_eq0 x (syn_ccom (syn_c0) A) dv_cache_0001
  have p0001 := @g_noel (syn_cop (.cv y) (syn_cproj2 (.cv x)))
  have p0002 := (Nominal.biimpRefl (syn_wbr (.cv y) (syn_c0) (syn_cproj2 (.cv x))))
  have p0003 :=
    @g_mtbir (syn_wbr (.cv y) (syn_c0) (syn_cproj2 (.cv x)))
      (.classMem (syn_cop (.cv y) (syn_cproj2 (.cv x))) (syn_c0)) p0001 p0002
  have p0004 :=
    @g_intnan (syn_wbr (.cv y) (syn_c0) (syn_cproj2 (.cv x)))
      (syn_wbr (syn_cproj1 (.cv x)) A (.cv y)) p0003
  have p0005 :=
    @g_nex
      (syn_wa (syn_wbr (syn_cproj1 (.cv x)) A (.cv y))
        (syn_wbr (.cv y) (syn_c0) (syn_cproj2 (.cv x))))
      y p0004
  have p0006 := @g_opeq (.cv x)
  have p0007 :=
    @g_eleq1i (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
      (syn_ccom (syn_c0) A) p0006
  have p0008 :=
    @g_opelco y (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)) (syn_c0) A dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    @g_bitri (.classMem (.cv x) (syn_ccom (syn_c0) A))
      (.classMem (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_ccom (syn_c0) A))
      (syn_wex y (syn_wa (syn_wbr (syn_cproj1 (.cv x)) A (.cv y))
          (syn_wbr (.cv y) (syn_c0) (syn_cproj2 (.cv x)))))
      p0007 p0008
  have p0010 :=
    @g_mtbir (.classMem (.cv x) (syn_ccom (syn_c0) A))
      (syn_wex y (syn_wa (syn_wbr (syn_cproj1 (.cv x)) A (.cv y))
          (syn_wbr (.cv y) (syn_c0) (syn_cproj2 (.cv x)))))
      p0005 p0009
  have p0011 :=
    @g_mpgbir (.classEq (syn_ccom (syn_c0) A) (syn_c0))
      (.neg (.classMem (.cv x) (syn_ccom (syn_c0) A))) x p0000 p0010
  exact p0011

@[expose]
noncomputable def g_coi1 (A : Class) : Nominal.NPrf (.classEq (syn_ccom A (syn_cid)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cid)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wbr (.cv x) A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_ccom A (syn_cid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccom A (syn_cid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_brco z (.cv x) (.cv y) A (syn_cid) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @g_vex z
  have p0002 := @g_ideq (.cv x) (.cv z) p0001
  have p0003 := @g_equcom x z
  have p0004_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv z)) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0004 :=
    @g_bitri (syn_wbr (.cv x) (syn_cid) (.cv z)) (.objEq x z) (.objEq z x)
      p0004_e00_recanon p0003
  have p0005 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_cid) (.cv z)) (.objEq z x) (syn_wbr (.cv z) A (.cv y))
      p0004
  have p0006 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) (syn_cid) (.cv z)) (syn_wbr (.cv z) A (.cv y)))
      (syn_wa (.objEq z x) (syn_wbr (.cv z) A (.cv y))) z p0005
  have p0007 := @g_vex x
  have p0008 := @g_breq1 (.cv z) (.cv x) (.cv y) A
  have p0009 :=
    @g_ceqsexv (syn_wbr (.cv z) A (.cv y)) (syn_wbr (.cv x) A (.cv y)) z (.cv x)
      dv_cache_0001 dv_cache_0005 p0007 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex z (syn_wa (.objEq z x) (syn_wbr (.cv z) A (.cv y))))
        (syn_wbr (.cv x) A (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
          syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccom A (syn_cid)) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_cid) (.cv z)) (syn_wbr (.cv z) A (.cv y))))
      (syn_wex z (syn_wa (.objEq z x) (syn_wbr (.cv z) A (.cv y))))
      (syn_wbr (.cv x) A (.cv y)) p0000 p0006 p0010_e02_recanon
  have p0011 :=
    @g_eqbrriv x y (syn_ccom A (syn_cid)) A dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0010
  exact p0011

@[expose]
noncomputable def g_coi2 (A : Class) : Nominal.NPrf (.classEq (syn_ccom (syn_cid) A) A) :=
  by
  have p0000 := @g_cnvco (syn_cid) A
  have p0001 := @g_cnvi
  have p0002 := @g_coeq2i (syn_ccnv (syn_cid)) (syn_cid) (syn_ccnv A) p0001
  have p0003 := @g_coi1 (syn_ccnv A)
  have p0004 :=
    @g_n_3eqtri (syn_ccnv (syn_ccom (syn_cid) A))
      (syn_ccom (syn_ccnv A) (syn_ccnv (syn_cid))) (syn_ccom (syn_ccnv A) (syn_cid))
      (syn_ccnv A) p0000 p0002 p0003
  have p0005 := @g_cnveqb (syn_ccom (syn_cid) A) A
  have p0006 :=
    @g_mpbir (.classEq (syn_ccom (syn_cid) A) A)
      (.classEq (syn_ccnv (syn_ccom (syn_cid) A)) (syn_ccnv A)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_coass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_ccom (syn_ccom A B) C) (syn_ccom A (syn_ccom B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
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
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0003 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0004 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_wbr (.cv x) C (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0008 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0009 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_wbr (.cv w) A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_y, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_ccom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_ccom B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_w_not_B, fresh_w_not_C, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_ccom (syn_ccom A B) C)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_ccom (syn_ccom A B) C)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_ccom A (syn_ccom B C))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_ccom A (syn_ccom B C))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0019 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_excom
      (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
        (syn_wbr (.cv w) A (.cv y)))
      w z
  have p0001 :=
    @g_anass (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w))
      (syn_wbr (.cv w) A (.cv y))
  have p0002 :=
    @g_n_2exbii
      (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
        (syn_wbr (.cv w) A (.cv y)))
      (syn_wa (syn_wbr (.cv x) C (.cv z))
        (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y))))
      z w p0001
  have p0003 :=
    @g_bitr2i
      (syn_wex w (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
            (syn_wbr (.cv w) A (.cv y)))))
      (syn_wex z (syn_wex w
          (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
            (syn_wbr (.cv w) A (.cv y)))))
      (syn_wex z (syn_wex w (syn_wa (syn_wbr (.cv x) C (.cv z))
            (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y))))))
      p0000 p0002
  have p0004 :=
    @g_brco w (.cv z) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_anbi2i (syn_wbr (.cv z) (syn_ccom A B) (.cv y))
      (syn_wex w (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y))))
      (syn_wbr (.cv x) C (.cv z)) p0004
  have p0006 :=
    @g_n_19_42v (syn_wbr (.cv x) C (.cv z))
      (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y))) w dv_cache_0005
  have p0007 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) (syn_ccom A B) (.cv y)))
      (syn_wa (syn_wbr (.cv x) C (.cv z))
        (syn_wex w (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y)))))
      (syn_wex w (syn_wa (syn_wbr (.cv x) C (.cv z))
          (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y)))))
      p0005 p0006
  have p0008 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) (syn_ccom A B) (.cv y)))
      (syn_wex w (syn_wa (syn_wbr (.cv x) C (.cv z))
          (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y)))))
      z p0007
  have p0009 :=
    @g_brco z (.cv x) (.cv w) B C dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0010 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_ccom B C) (.cv w))
      (syn_wex z (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w))))
      (syn_wbr (.cv w) A (.cv y)) p0009
  have p0011 :=
    @g_n_19_41v (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
      (syn_wbr (.cv w) A (.cv y)) z dv_cache_0010
  have p0012 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) (syn_ccom B C) (.cv w)) (syn_wbr (.cv w) A (.cv y)))
      (syn_wa (syn_wex z (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w))))
        (syn_wbr (.cv w) A (.cv y)))
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
          (syn_wbr (.cv w) A (.cv y))))
      p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) (syn_ccom B C) (.cv w)) (syn_wbr (.cv w) A (.cv y)))
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
          (syn_wbr (.cv w) A (.cv y))))
      w p0012
  have p0014 :=
    @g_n_3bitr4i
      (syn_wex z (syn_wex w (syn_wa (syn_wbr (.cv x) C (.cv z))
            (syn_wa (syn_wbr (.cv z) B (.cv w)) (syn_wbr (.cv w) A (.cv y))))))
      (syn_wex w (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) B (.cv w)))
            (syn_wbr (.cv w) A (.cv y)))))
      (syn_wex z (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) (syn_ccom A B) (.cv y))))
      (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_ccom B C) (.cv w)) (syn_wbr (.cv w) A (.cv y))))
      p0003 p0008 p0013
  have p0015 :=
    @g_brco z (.cv x) (.cv y) (syn_ccom A B) C dv_cache_0006 dv_cache_0011 dv_cache_0012
      dv_cache_0009
  have p0016 :=
    @g_brco w (.cv x) (.cv y) A (syn_ccom B C) dv_cache_0013 dv_cache_0002 dv_cache_0003
      dv_cache_0014
  have p0017 :=
    @g_n_3bitr4i
      (syn_wex z (syn_wa (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv z) (syn_ccom A B) (.cv y))))
      (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_ccom B C) (.cv w)) (syn_wbr (.cv w) A (.cv y))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom A B) C) (.cv y))
      (syn_wbr (.cv x) (syn_ccom A (syn_ccom B C)) (.cv y)) p0014 p0015 p0016
  have p0018 :=
    @g_eqbrriv x y (syn_ccom (syn_ccom A B) C) (syn_ccom A (syn_ccom B C)) dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ssdmrn (A : Class) :
    Nominal.NPrf (syn_wss A (syn_cxp (syn_cdm A) (syn_crn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cxp (syn_cdm A) (syn_crn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cxp (syn_cdm A) (syn_crn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_ssrel x y A (syn_cxp (syn_cdm A) (syn_crn A)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @g_opeldm (.cv x) (.cv y) A
  have p0002 := @g_opelrn (.cv x) (.cv y) A
  have p0003 := @g_opelxp (.cv x) (.cv y) (syn_cdm A) (syn_crn A)
  have p0004 :=
    @g_sylanbrc (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (.cv x) (syn_cdm A))
      (.classMem (.cv y) (syn_crn A))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cdm A) (syn_crn A))) p0001 p0002
      p0003
  have p0005 := Nominal.gen p0004 y
  have p0006 :=
    @g_mpgbir (syn_wss A (syn_cxp (syn_cdm A) (syn_crn A)))
      (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cdm A) (syn_crn A)))))
      x p0000 p0005
  exact p0006

@[expose]
noncomputable def g_dfcnv2 (A : Class) :
    Nominal.NPrf (.classEq (syn_ccnv A) (syn_cima (syn_cswap) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((syn_cop (.cv y) (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classMem (syn_cop (.cv y) (.cv x)) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cswap)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ ((syn_ccnv A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccnv A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cima (syn_cswap) A)).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cima (syn_cswap) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_vex x
  have p0001 := @g_vex y
  have p0002 := @g_brswap2 (.cv z) (.cv x) (.cv y) p0000 p0001
  have p0003 :=
    @g_anbi1i (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))
      (.classEq (.cv z) (syn_cop (.cv y) (.cv x))) (.classMem (.cv z) A) p0002
  have p0004 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) (.classMem (.cv z) A))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv y) (.cv x))) (.classMem (.cv z) A)) z p0003
  have p0005 := @g_opex (.cv y) (.cv x) p0001 p0000
  have p0006 := @g_eleq1 (.cv z) (syn_cop (.cv y) (.cv x)) A
  have p0007 :=
    @g_ceqsexv (.classMem (.cv z) A) (.classMem (syn_cop (.cv y) (.cv x)) A) z
      (syn_cop (.cv y) (.cv x)) dv_cache_0001 dv_cache_0002 p0005 p0006
  have p0008 :=
    @g_bitri
      (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cop (.cv y) (.cv x))) (.classMem (.cv z) A)))
      (.classMem (syn_cop (.cv y) (.cv x)) A) p0004 p0007
  have p0009 :=
    @g_elima z (syn_cop (.cv x) (.cv y)) (syn_cswap) A dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0010 :=
    (Nominal.biimpRefl (syn_wrex z A (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))))
  have p0011 :=
    @g_exancom (.classMem (.cv z) A)
      (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))) z
  have p0012 :=
    @g_bitri (syn_wrex z A (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv z) A)
          (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))))
      (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      p0010 p0011
  have p0013 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_cswap) A))
      (syn_wrex z A (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y))))
      (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      p0009 p0012
  have p0014 := @g_opelcnv (.cv x) (.cv y) A
  have p0015 :=
    @g_n_3bitr4ri
      (syn_wex z (syn_wa (syn_wbr (.cv z) (syn_cswap) (syn_cop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      (.classMem (syn_cop (.cv y) (.cv x)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_cswap) A))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A)) p0008 p0013 p0014
  have p0016 :=
    @g_eqrelriv x y (syn_ccnv A) (syn_cima (syn_cswap) A) dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0015
  exact p0016

@[expose]
noncomputable def g_cnvexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_ccnv A) (syn_cvv))) :=
  by
  have p0000 := @g_dfcnv2 A
  have p0001 := @g_swapex
  have p0002 := @g_imaexg (syn_cswap) A (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cswap) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cima (syn_cswap) A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_ccnv A) (syn_cima (syn_cswap) A) (syn_cvv) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_cnvex (A : Class)
    (hyp_cnvex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccnv A) (syn_cvv)) :=
  by
  have p0000 := @g_cnvexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_cnvex_1 p0000
  exact p0001

@[expose]
noncomputable def g_rnexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_crn A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_crn A))
  have p0001 := @g_vvex
  have p0002 := @g_imaexg A (syn_cvv) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cima A (syn_cvv)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_crn A) (syn_cima A (syn_cvv)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_dmexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cdm A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cdm A))
  have p0001 := @g_cnvexg A V
  have p0002 := @g_rnexg (syn_ccnv A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A V) (.classMem (syn_ccnv A) (syn_cvv))
      (.classMem (syn_crn (syn_ccnv A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_cdm A) (syn_crn (syn_ccnv A)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_dmex (A : Class) (hyp_dmex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cdm A) (syn_cvv)) :=
  by
  have p0000 := @g_dmexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_dmex_1 p0000
  exact p0001

@[expose]
noncomputable def g_rnex (A : Class) (hyp_dmex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_crn A) (syn_cvv)) :=
  by
  have p0000 := @g_rnexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_dmex_1 p0000
  exact p0001

@[expose]
noncomputable def g_df2nd2 :
    Nominal.NPrf (.classEq (syn_c2nd) (syn_ccom (syn_c1st) (syn_cswap))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : z ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wbr (.cv x) (syn_cswap) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_w, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_cop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_wbr (.cv x) (syn_cswap) (syn_cop (.cv y) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ ((syn_c1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_c1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_c1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cswap)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cswap)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_cswap)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0016 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have p0000 := @g_vex y
  have p0001 := @g_br1st z (.cv w) (.cv y) dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @g_anbi1i (syn_wbr (.cv w) (syn_c1st) (.cv y))
      (syn_wex z (.classEq (.cv w) (syn_cop (.cv y) (.cv z))))
      (syn_wbr (.cv x) (syn_cswap) (.cv w)) p0001
  have p0003 :=
    @g_ancom (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y))
  have p0004 :=
    @g_n_19_41v (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (.cv x) (syn_cswap) (.cv w)) z dv_cache_0003
  have p0005 :=
    @g_n_3bitr4i
      (syn_wa (syn_wbr (.cv w) (syn_c1st) (.cv y)) (syn_wbr (.cv x) (syn_cswap) (.cv w)))
      (syn_wa (syn_wex z (.classEq (.cv w) (syn_cop (.cv y) (.cv z))))
        (syn_wbr (.cv x) (syn_cswap) (.cv w)))
      (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y)))
      (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
          (syn_wbr (.cv x) (syn_cswap) (.cv w))))
      p0002 p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w)) (syn_wbr (.cv w) (syn_c1st) (.cv y)))
      (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
          (syn_wbr (.cv x) (syn_cswap) (.cv w))))
      w p0005
  have p0007 :=
    @g_excom
      (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
        (syn_wbr (.cv x) (syn_cswap) (.cv w)))
      z w
  have p0008 := @g_vex z
  have p0009 := @g_opex (.cv y) (.cv z) p0000 p0008
  have p0010 := @g_breq2 (.cv w) (syn_cop (.cv y) (.cv z)) (.cv x) (syn_cswap)
  have p0011 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_cswap) (.cv w))
      (syn_wbr (.cv x) (syn_cswap) (syn_cop (.cv y) (.cv z))) w (syn_cop (.cv y) (.cv z))
      dv_cache_0004 dv_cache_0005 p0009 p0010
  have p0012 := @g_brswap2 (.cv x) (.cv y) (.cv z) p0000 p0008
  have p0013 :=
    @g_bitri
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
          (syn_wbr (.cv x) (syn_cswap) (.cv w))))
      (syn_wbr (.cv x) (syn_cswap) (syn_cop (.cv y) (.cv z)))
      (.classEq (.cv x) (syn_cop (.cv z) (.cv y))) p0011 p0012
  have p0014 :=
    @g_exbii
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
          (syn_wbr (.cv x) (syn_cswap) (.cv w))))
      (.classEq (.cv x) (syn_cop (.cv z) (.cv y))) z p0013
  have p0015 :=
    @g_n_3bitr2ri
      (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w))
          (syn_wbr (.cv w) (syn_c1st) (.cv y))))
      (syn_wex w (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
            (syn_wbr (.cv x) (syn_cswap) (.cv w)))))
      (syn_wex z (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
            (syn_wbr (.cv x) (syn_cswap) (.cv w)))))
      (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y)))) p0006 p0007 p0014
  have p0016 :=
    @g_opabbii (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y))))
      (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w))
          (syn_wbr (.cv w) (syn_c1st) (.cv y))))
      x y p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_2nd x y z
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x y w (syn_c1st)
      (syn_cswap) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0016
  have p0019 :=
    @g_n_3eqtr4i (syn_copab x y (syn_wex z (.classEq (.cv x) (syn_cop (.cv z) (.cv y)))))
      (syn_copab x y (syn_wex w (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv w))
            (syn_wbr (.cv w) (syn_c1st) (.cv y)))))
      (syn_c2nd) (syn_ccom (syn_c1st) (syn_cswap)) p0016 p0017 p0018
  exact p0019

@[expose]
noncomputable def g_n_2ndex : Nominal.NPrf (.classMem (syn_c2nd) (syn_cvv)) :=
  by
  have p0000 := @g_df2nd2
  have p0001 := @g_n_1stex
  have p0002 := @g_swapex
  have p0003 := @g_coex (syn_c1st) (syn_cswap) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_c2nd) (syn_ccom (syn_c1st) (syn_cswap)) (syn_cvv) p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
