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

/-- Checked nominal proof certificate identified upstream as `g_dmcoss`. -/
@[expose]
noncomputable def gDmcoss (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCdm (synCcom A B)) (synCdm B)) :=
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
  have dv_cache_0005 : y ∉ ((synWbr (.cv x) B (.cv z))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCcom A B)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCdm (synCcom A B))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCdm B)).fv :=
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
    @gBrco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @gExbii (synWbr (.cv x) (synCcom A B) (.cv y))
      (synWex z (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))) y p0000
  have p0002 :=
    @gExcom (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y))) y z
  have p0003 :=
    @gBitri (synWex y (synWbr (.cv x) (synCcom A B) (.cv y)))
      (synWex y (synWex z (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))))
      (synWex z (synWex y (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))))
      p0001 p0002
  have p0004 := @gSimpl (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y))
  have p0005 :=
    @gExlimiv (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
      (synWbr (.cv x) B (.cv z)) y dv_cache_0005 p0004
  have p0006 :=
    @gEximi (synWex y (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y))))
      (synWbr (.cv x) B (.cv z)) z p0005
  have p0007 :=
    @gSylbi (synWex y (synWbr (.cv x) (synCcom A B) (.cv y)))
      (synWex z (synWex y (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))))
      (synWex z (synWbr (.cv x) B (.cv z))) p0003 p0006
  have p0008 := @gEldm y (.cv x) (synCcom A B) dv_cache_0006 dv_cache_0007
  have p0009 := @gEldm z (.cv x) B dv_cache_0001 dv_cache_0004
  have p0010 :=
    @gN3imtr4i (synWex y (synWbr (.cv x) (synCcom A B) (.cv y)))
      (synWex z (synWbr (.cv x) B (.cv z))) (.classMem (.cv x) (synCdm (synCcom A B)))
      (.classMem (.cv x) (synCdm B)) p0007 p0008 p0009
  have p0011 :=
    @gSsriv x (synCdm (synCcom A B)) (synCdm B) dv_cache_0008 dv_cache_0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_rncoss`. -/
@[expose]
noncomputable def gRncoss (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCrn (synCcom A B)) (synCrn A)) :=
  by
  have p0000 := @gDmcoss (synCcnv B) (synCcnv A)
  have p0001 := @gDfrn4 (synCcom A B)
  have p0002 := @gCnvco A B
  have p0003 :=
    @gDmeqi (synCcnv (synCcom A B)) (synCcom (synCcnv B) (synCcnv A)) p0002
  have p0004 :=
    @gEqtri (synCrn (synCcom A B)) (synCdm (synCcnv (synCcom A B)))
      (synCdm (synCcom (synCcnv B) (synCcnv A))) p0001 p0003
  have p0005 := @gDfrn4 A
  have p0006 :=
    @gN3sstr4i (synCdm (synCcom (synCcnv B) (synCcnv A))) (synCdm (synCcnv A))
      (synCrn (synCcom A B)) (synCrn A) p0000 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_dmcosseq`. -/
@[expose]
noncomputable def gDmcosseq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWss (synCrn B) (synCdm A))
        (.classEq (synCdm (synCcom A B)) (synCdm B))) :=
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
  have dv_cache_0003 : z ∉ ((synWbr (.cv x) B (.cv y))).fv :=
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
  have dv_cache_0004 : y ∉ ((synWss (synCrn B) (synCdm A))).fv :=
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
  have dv_cache_0010 : z ∉ ((synCcom A B)).fv :=
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
  have dv_cache_0011 : x ∉ ((synCdm B)).fv :=
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
  have dv_cache_0012 : x ∉ ((synCdm (synCcom A B))).fv :=
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
  have dv_cache_0013 : x ∉ ((synWss (synCrn B) (synCdm A))).fv :=
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
  have p0000 := @gDmcoss A B
  have p0001 :=
    @gA1i (synWss (synCdm (synCcom A B)) (synCdm B))
      (synWss (synCrn B) (synCdm A)) p0000
  have p0002 := @gBrelrn (.cv x) (.cv y) B
  have p0003 := @gSsel (synCrn B) (synCdm A) (.cv y)
  have p0004 :=
    @gSyl5 (synWbr (.cv x) B (.cv y)) (.classMem (.cv y) (synCrn B))
      (synWss (synCrn B) (synCdm A)) (.classMem (.cv y) (synCdm A)) p0002 p0003
  have p0005 := @gEldm z (.cv y) A dv_cache_0001 dv_cache_0002
  have p0006 :=
    @gSyl6ib (synWss (synCrn B) (synCdm A)) (synWbr (.cv x) B (.cv y))
      (.classMem (.cv y) (synCdm A)) (synWex z (synWbr (.cv y) A (.cv z))) p0004 p0005
  have p0007 :=
    @gAncld (synWss (synCrn B) (synCdm A)) (synWbr (.cv x) B (.cv y))
      (synWex z (synWbr (.cv y) A (.cv z))) p0006
  have p0008 :=
    @gN1942v (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)) z dv_cache_0003
  have p0009 :=
    @gSyl6ibr (synWss (synCrn B) (synCdm A)) (synWbr (.cv x) B (.cv y))
      (synWa (synWbr (.cv x) B (.cv y)) (synWex z (synWbr (.cv y) A (.cv z))))
      (synWex z (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)))) p0007
      p0008
  have p0010 :=
    @gEximdv (synWss (synCrn B) (synCdm A)) (synWbr (.cv x) B (.cv y))
      (synWex z (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)))) y
      dv_cache_0004 p0009
  have p0011 :=
    @gBrco y (.cv x) (.cv z) A B dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0012 :=
    @gExbii (synWbr (.cv x) (synCcom A B) (.cv z))
      (synWex y (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)))) z p0011
  have p0013 :=
    @gExcom (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z))) z y
  have p0014 :=
    @gBitri (synWex z (synWbr (.cv x) (synCcom A B) (.cv z)))
      (synWex z (synWex y (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)))))
      (synWex y (synWex z (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)))))
      p0012 p0013
  have p0015 :=
    @gSyl6ibr (synWss (synCrn B) (synCdm A)) (synWex y (synWbr (.cv x) B (.cv y)))
      (synWex y (synWex z (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) A (.cv z)))))
      (synWex z (synWbr (.cv x) (synCcom A B) (.cv z))) p0010 p0014
  have p0016 := @gEldm y (.cv x) B dv_cache_0005 dv_cache_0008
  have p0017 := @gEldm z (.cv x) (synCcom A B) dv_cache_0009 dv_cache_0010
  have p0018 :=
    @gN3imtr4g (synWss (synCrn B) (synCdm A)) (synWex y (synWbr (.cv x) B (.cv y)))
      (synWex z (synWbr (.cv x) (synCcom A B) (.cv z))) (.classMem (.cv x) (synCdm B))
      (.classMem (.cv x) (synCdm (synCcom A B))) p0015 p0016 p0017
  have p0019 :=
    @gSsrdv (synWss (synCrn B) (synCdm A)) x (synCdm B) (synCdm (synCcom A B))
      dv_cache_0011 dv_cache_0012 dv_cache_0013 p0018
  have p0020 :=
    @gEqssd (synWss (synCrn B) (synCdm A)) (synCdm (synCcom A B)) (synCdm B) p0001
      p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_dmcoeq`. -/
@[expose]
noncomputable def gDmcoeq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classEq (synCdm A) (synCrn B))
        (.classEq (synCdm (synCcom A B)) (synCdm B))) :=
  by
  have p0000 := @gEqimss2 (synCrn B) (synCdm A)
  have p0001 := @gDmcosseq A B
  have p0002 :=
    @gSyl (.classEq (synCdm A) (synCrn B)) (synWss (synCrn B) (synCdm A))
      (.classEq (synCdm (synCcom A B)) (synCdm B)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rncoeq`. -/
@[expose]
noncomputable def gRncoeq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classEq (synCdm A) (synCrn B))
        (.classEq (synCrn (synCcom A B)) (synCrn A))) :=
  by
  have p0000 := @gDmcoeq (synCcnv B) (synCcnv A)
  have p0001 := (Nominal.classEqRefl (synCdm A))
  have p0002 := @gDfrn4 B
  have p0003 :=
    @gEqeq12i (synCdm A) (synCrn (synCcnv A)) (synCrn B) (synCdm (synCcnv B)) p0001
      p0002
  have p0004 := @gEqcom (synCrn (synCcnv A)) (synCdm (synCcnv B))
  have p0005 :=
    @gBitri (.classEq (synCdm A) (synCrn B))
      (.classEq (synCrn (synCcnv A)) (synCdm (synCcnv B)))
      (.classEq (synCdm (synCcnv B)) (synCrn (synCcnv A))) p0003 p0004
  have p0006 := @gDfrn4 (synCcom A B)
  have p0007 := @gCnvco A B
  have p0008 :=
    @gDmeqi (synCcnv (synCcom A B)) (synCcom (synCcnv B) (synCcnv A)) p0007
  have p0009 :=
    @gEqtri (synCrn (synCcom A B)) (synCdm (synCcnv (synCcom A B)))
      (synCdm (synCcom (synCcnv B) (synCcnv A))) p0006 p0008
  have p0010 := @gDfrn4 A
  have p0011 :=
    @gEqeq12i (synCrn (synCcom A B)) (synCdm (synCcom (synCcnv B) (synCcnv A)))
      (synCrn A) (synCdm (synCcnv A)) p0009 p0010
  have p0012 :=
    @gN3imtr4i (.classEq (synCdm (synCcnv B)) (synCrn (synCcnv A)))
      (.classEq (synCdm (synCcom (synCcnv B) (synCcnv A))) (synCdm (synCcnv A)))
      (.classEq (synCdm A) (synCrn B)) (.classEq (synCrn (synCcom A B)) (synCrn A))
      p0000 p0005 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_res0`. -/
@[expose]
noncomputable def gRes0 (A : Class) :
    Nominal.NPrf (.classEq (synCres A (synC0)) (synC0)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCres A (synC0)))
  have p0001 := @gXp0r (synCvv)
  have p0002 := @gIneq2i (synCxp (synC0) (synCvv)) (synC0) A p0001
  have p0003 := @gIn0 A
  have p0004 :=
    @gN3eqtri (synCres A (synC0)) (synCin A (synCxp (synC0) (synCvv)))
      (synCin A (synC0)) (synC0) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_resundi`. -/
@[expose]
noncomputable def gResundi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCres A (synCun B C)) (synCun (synCres A B) (synCres A C))) :=
  by
  have p0000 := @gXpundir B C (synCvv)
  have p0001 :=
    @gIneq2i (synCxp (synCun B C) (synCvv))
      (synCun (synCxp B (synCvv)) (synCxp C (synCvv))) A p0000
  have p0002 := @gIndi A (synCxp B (synCvv)) (synCxp C (synCvv))
  have p0003 :=
    @gEqtri (synCin A (synCxp (synCun B C) (synCvv)))
      (synCin A (synCun (synCxp B (synCvv)) (synCxp C (synCvv))))
      (synCun (synCin A (synCxp B (synCvv))) (synCin A (synCxp C (synCvv)))) p0001
      p0002
  have p0004 := (Nominal.classEqRefl (synCres A (synCun B C)))
  have p0005 := (Nominal.classEqRefl (synCres A B))
  have p0006 := (Nominal.classEqRefl (synCres A C))
  have p0007 :=
    @gUneq12i (synCres A B) (synCin A (synCxp B (synCvv))) (synCres A C)
      (synCin A (synCxp C (synCvv))) p0005 p0006
  have p0008 :=
    @gN3eqtr4i (synCin A (synCxp (synCun B C) (synCvv)))
      (synCun (synCin A (synCxp B (synCvv))) (synCin A (synCxp C (synCvv))))
      (synCres A (synCun B C)) (synCun (synCres A B) (synCres A C)) p0003 p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_resundir`. -/
@[expose]
noncomputable def gResundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCres (synCun A B) C) (synCun (synCres A C) (synCres B C))) :=
  by
  have p0000 := @gIndir A B (synCxp C (synCvv))
  have p0001 := (Nominal.classEqRefl (synCres (synCun A B) C))
  have p0002 := (Nominal.classEqRefl (synCres A C))
  have p0003 := (Nominal.classEqRefl (synCres B C))
  have p0004 :=
    @gUneq12i (synCres A C) (synCin A (synCxp C (synCvv))) (synCres B C)
      (synCin B (synCxp C (synCvv))) p0002 p0003
  have p0005 :=
    @gN3eqtr4i (synCin (synCun A B) (synCxp C (synCvv)))
      (synCun (synCin A (synCxp C (synCvv))) (synCin B (synCxp C (synCvv))))
      (synCres (synCun A B) C) (synCun (synCres A C) (synCres B C)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dmres`. -/
@[expose]
noncomputable def gDmres (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCdm (synCres A B)) (synCin B (synCdm A))) :=
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
  have dv_cache_0003 : y ∉ ((synCres A B)).fv :=
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
  have dv_cache_0005 : x ∉ ((synCdm A)).fv :=
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
  have dv_cache_0007 : x ∉ ((synCdm (synCres A B))).fv :=
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
    @gN1941v (synWbr (.cv x) A (.cv y)) (.classMem (.cv x) B) y dv_cache_0001
  have p0001 := @gEldm y (.cv x) (synCres A B) dv_cache_0002 dv_cache_0003
  have p0002 := @gBrres (.cv x) (.cv y) A B
  have p0003 :=
    @gExbii (synWbr (.cv x) (synCres A B) (.cv y))
      (synWa (synWbr (.cv x) A (.cv y)) (.classMem (.cv x) B)) y p0002
  have p0004 :=
    @gBitri (.classMem (.cv x) (synCdm (synCres A B)))
      (synWex y (synWbr (.cv x) (synCres A B) (.cv y)))
      (synWex y (synWa (synWbr (.cv x) A (.cv y)) (.classMem (.cv x) B))) p0001 p0003
  have p0005 := @gEldm y (.cv x) A dv_cache_0002 dv_cache_0004
  have p0006 :=
    @gAnbi1i (.classMem (.cv x) (synCdm A)) (synWex y (synWbr (.cv x) A (.cv y)))
      (.classMem (.cv x) B) p0005
  have p0007 :=
    @gN3bitr4ri (synWex y (synWa (synWbr (.cv x) A (.cv y)) (.classMem (.cv x) B)))
      (synWa (synWex y (synWbr (.cv x) A (.cv y))) (.classMem (.cv x) B))
      (.classMem (.cv x) (synCdm (synCres A B)))
      (synWa (.classMem (.cv x) (synCdm A)) (.classMem (.cv x) B)) p0000 p0004 p0006
  have p0008 :=
    @gIneqri x (synCdm A) B (synCdm (synCres A B)) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0007
  have p0009 := @gIncom (synCdm A) B
  have p0010 :=
    @gEqtr3i (synCin (synCdm A) B) (synCdm (synCres A B)) (synCin B (synCdm A))
      p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ssdmres`. -/
@[expose]
noncomputable def gSsdmres (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWss A (synCdm B)) (.classEq (synCdm (synCres B A)) A)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWss A (synCdm B)))
  have p0001 := @gDmres B A
  have p0002 := @gEqeq1i (synCdm (synCres B A)) (synCin A (synCdm B)) A p0001
  have p0003 :=
    @gBitr4i (synWss A (synCdm B)) (.classEq (synCin A (synCdm B)) A)
      (.classEq (synCdm (synCres B A)) A) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_resss`. -/
@[expose]
noncomputable def gResss (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCres A B) A) :=
  by
  have p0000 := (Nominal.classEqRefl (synCres A B))
  have p0001 := @gInss1 A (synCxp B (synCvv))
  have p0002 := @gEqsstri (synCres A B) (synCin A (synCxp B (synCvv))) A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ssres2`. -/
@[expose]
noncomputable def gSsres2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCres C A) (synCres C B))) :=
  by
  have p0000 := @gXpss1 A B (synCvv)
  have p0001 := @gSslin (synCxp A (synCvv)) (synCxp B (synCvv)) C
  have p0002 :=
    @gSyl (synWss A B) (synWss (synCxp A (synCvv)) (synCxp B (synCvv)))
      (synWss (synCin C (synCxp A (synCvv))) (synCin C (synCxp B (synCvv)))) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (synCres C A))
  have p0004 := (Nominal.classEqRefl (synCres C B))
  have p0005 :=
    @gN3sstr4g (synWss A B) (synCin C (synCxp A (synCvv)))
      (synCin C (synCxp B (synCvv))) (synCres C A) (synCres C B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ssreseq`. -/
@[expose]
noncomputable def gSsreseq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss (synCdm A) B) (.classEq (synCres A B) A)) :=
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
  have dv_cache_0003 : x ∉ ((synCres A B)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCres A B)).fv :=
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
  have dv_cache_0005 : x ∉ ((synWss (synCdm A) B)).fv :=
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
  have dv_cache_0006 : y ∉ ((synWss (synCdm A) B)).fv :=
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
  have p0000 := @gResss A B
  have p0001 := @gA1i (synWss (synCres A B) A) (synWss (synCdm A) B) p0000
  have p0002 := @gOpeldm (.cv x) (.cv y) A
  have p0003 := @gSsel (synCdm A) B (.cv x)
  have p0004 :=
    @gSyl5 (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (.cv x) (synCdm A))
      (synWss (synCdm A) B) (.classMem (.cv x) B) p0002 p0003
  have p0005 :=
    @gAncld (synWss (synCdm A) B) (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (.cv x) B) p0004
  have p0006 := @gOpelres (.cv x) (.cv y) A B
  have p0007 :=
    @gSyl6ibr (synWss (synCdm A) B) (.classMem (synCop (.cv x) (.cv y)) A)
      (synWa (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (.cv x) B))
      (.classMem (synCop (.cv x) (.cv y)) (synCres A B)) p0005 p0006
  have p0008 :=
    @gRelssdv (synWss (synCdm A) B) x y A (synCres A B) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0007
  have p0009 := @gEqssd (synWss (synCdm A) B) (synCres A B) A p0001 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_resopab`. -/
@[expose]
noncomputable def gResopab (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCres (synCopab x y ph) A)
        (synCopab x y (synWa (.classMem (.cv x) A) ph))) :=
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
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := (Nominal.classEqRefl (synCres (synCopab x y ph) A))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 := @gVex y
  have p0003 := @gBiantru (.classMem (.cv y) (synCvv)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @gOpabbii (.classMem (.cv x) A)
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCvv))) x y p0003
  have p0005 :=
    @gEqtr4i (synCxp A (synCvv))
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCvv))))
      (synCopab x y (.classMem (.cv x) A)) p0001 p0004
  have p0006 :=
    @gIneq2i (synCxp A (synCvv)) (synCopab x y (.classMem (.cv x) A))
      (synCopab x y ph) p0005
  have p0007 := @gIncom (synCopab x y ph) (synCopab x y (.classMem (.cv x) A))
  have p0008 :=
    @gEqtri (synCin (synCopab x y ph) (synCxp A (synCvv)))
      (synCin (synCopab x y ph) (synCopab x y (.classMem (.cv x) A)))
      (synCin (synCopab x y (.classMem (.cv x) A)) (synCopab x y ph)) p0006 p0007
  have p0009 := @gInopab (.classMem (.cv x) A) ph x y dv_cache_0005
  have p0010 :=
    @gN3eqtri (synCres (synCopab x y ph) A)
      (synCin (synCopab x y ph) (synCxp A (synCvv)))
      (synCin (synCopab x y (.classMem (.cv x) A)) (synCopab x y ph))
      (synCopab x y (synWa (.classMem (.cv x) A) ph)) p0000 p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_iss`. -/
@[expose]
noncomputable def gIss (A : Class) :
    Nominal.NPrf
      (synWb (synWss A (synCid)) (.classEq A (synCres (synCid) (synCdm A)))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classMem (synCop (.cv x) (.cv x)) A)).fv :=
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
  have dv_cache_0004 : y ∉ ((synWss A (synCid))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCres (synCid) (synCdm A))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCres (synCid) (synCdm A))).fv :=
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
  have dv_cache_0008 : x ∉ ((synWss A (synCid))).fv :=
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
  have p0000 := @gSsel A (synCid) (synCop (.cv x) (.cv y))
  have p0001 := @gOpeldm (.cv x) (.cv y) A
  have p0002 :=
    @gA1i (.imp (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (.cv x) (synCdm A)))
      (synWss A (synCid)) p0001
  have p0003 :=
    @gJcad (synWss A (synCid)) (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.classMem (.cv x) (synCdm A))
      p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWbr (.cv x) (synCid) (.cv y)))
  have p0005 := @gVex y
  have p0006 := @gIdeq (.cv x) (.cv y) p0005
  have p0007_e01_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
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
    @gBitr3i (.classMem (synCop (.cv x) (.cv y)) (synCid))
      (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y) p0004 p0007_e01_recanon
  have p0008 :=
    @gAnbi1i (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.objEq x y)
      (.classMem (.cv x) (synCdm A)) p0007
  have p0009 := @gEldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0010 :=
    @gSyl6ib (synWss A (synCid)) (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.objEq x y) p0000 p0007
  have p0011 := @gOpeq2 (.cv x) (.cv y) (.cv x)
  have p0012_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (.classEq (synCop (.cv x) (.cv x)) (synCop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @gEleq1d (.objEq x y) (synCop (.cv x) (.cv x)) (synCop (.cv x) (.cv y)) A
      p0012_e00_recanon
  have p0013 :=
    @gBiimprd (.objEq x y) (.classMem (synCop (.cv x) (.cv x)) A)
      (.classMem (synCop (.cv x) (.cv y)) A) p0012
  have p0014 :=
    @gSyli (.classMem (synCop (.cv x) (.cv y)) A) (synWss A (synCid)) (.objEq x y)
      (.classMem (synCop (.cv x) (.cv x)) A) p0010 p0013
  have p0015 :=
    @gExlimdv (synWss A (synCid)) (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (.cv x) (.cv x)) A) y dv_cache_0003 dv_cache_0004 p0014
  have p0016 :=
    @gSyl5bi (.classMem (.cv x) (synCdm A))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) A)) (synWss A (synCid))
      (.classMem (synCop (.cv x) (.cv x)) A) p0009 p0015
  have p0017 :=
    @gBiimpd (.objEq x y) (.classMem (synCop (.cv x) (.cv x)) A)
      (.classMem (synCop (.cv x) (.cv y)) A) p0012
  have p0018 :=
    @gSyl9 (synWss A (synCid)) (.classMem (.cv x) (synCdm A))
      (.classMem (synCop (.cv x) (.cv x)) A) (.objEq x y)
      (.classMem (synCop (.cv x) (.cv y)) A) p0016 p0017
  have p0019 :=
    @gImp3a (synWss A (synCid)) (.objEq x y) (.classMem (.cv x) (synCdm A))
      (.classMem (synCop (.cv x) (.cv y)) A) p0018
  have p0020 :=
    @gSyl5bi
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.classMem (.cv x) (synCdm A)))
      (synWa (.objEq x y) (.classMem (.cv x) (synCdm A))) (synWss A (synCid))
      (.classMem (synCop (.cv x) (.cv y)) A) p0008 p0019
  have p0021 :=
    @gImpbid (synWss A (synCid)) (.classMem (synCop (.cv x) (.cv y)) A)
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.classMem (.cv x) (synCdm A)))
      p0003 p0020
  have p0022 := @gOpelres (.cv x) (.cv y) (synCid) (synCdm A)
  have p0023 :=
    @gSyl6bbr (synWss A (synCid)) (.classMem (synCop (.cv x) (.cv y)) A)
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.classMem (.cv x) (synCdm A)))
      (.classMem (synCop (.cv x) (.cv y)) (synCres (synCid) (synCdm A))) p0021 p0022
  have p0024 :=
    @gEqrelrdv (synWss A (synCid)) x y A (synCres (synCid) (synCdm A)) dv_cache_0005
      dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0004 dv_cache_0009
      p0023
  have p0025 := @gResss (synCid) (synCdm A)
  have p0026 := @gSseq1 A (synCres (synCid) (synCdm A)) (synCid)
  have p0027 :=
    @gMpbiri (.classEq A (synCres (synCid) (synCdm A))) (synWss A (synCid))
      (synWss (synCres (synCid) (synCdm A)) (synCid)) p0025 p0026
  have p0028 :=
    @gImpbii (synWss A (synCid)) (.classEq A (synCres (synCid) (synCdm A))) p0024
      p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_resopab2`. -/
@[expose]
noncomputable def gResopab2 (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWss A B)
        (.classEq (synCres (synCopab x y (synWa (.classMem (.cv x) B) ph)) A)
          (synCopab x y (synWa (.classMem (.cv x) A) ph)))) :=
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
  have dv_cache_0004 : x ∉ ((synWss A B)).fv :=
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
  have dv_cache_0005 : y ∉ ((synWss A B)).fv :=
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
    @gResopab (synWa (.classMem (.cv x) B) ph) x y A dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 := @gSsel A B (.cv x)
  have p0002 := @gPm471 (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0003 :=
    @gSylib (synWss A B) (.imp (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0001 p0002
  have p0004 :=
    @gAnbi1d (synWss A B) (.classMem (.cv x) A)
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) ph p0003
  have p0005 := @gAnass (.classMem (.cv x) A) (.classMem (.cv x) B) ph
  have p0006 :=
    @gSyl6rbb (synWss A B) (synWa (.classMem (.cv x) A) ph)
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) ph)
      (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) ph)) p0004 p0005
  have p0007 :=
    @gOpabbidv (synWss A B)
      (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) ph))
      (synWa (.classMem (.cv x) A) ph) x y dv_cache_0004 dv_cache_0005 p0006
  have p0008 :=
    @gSyl5eq (synWss A B) (synCres (synCopab x y (synWa (.classMem (.cv x) B) ph)) A)
      (synCopab x y (synWa (.classMem (.cv x) A) (synWa (.classMem (.cv x) B) ph)))
      (synCopab x y (synWa (.classMem (.cv x) A) ph)) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_dmresi`. -/
@[expose]
noncomputable def gDmresi (A : Class) :
    Nominal.NPrf (.classEq (synCdm (synCres (synCid) A)) A) :=
  by
  have p0000 := @gSsv A
  have p0001 := @gDmi
  have p0002 := @gSseqtr4i A (synCvv) (synCdm (synCid)) p0000 p0001
  have p0003 := @gSsdmres A (synCid)
  have p0004 :=
    @gMpbi (synWss A (synCdm (synCid))) (.classEq (synCdm (synCres (synCid) A)) A)
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_resid`. -/
@[expose]
noncomputable def gResid (A : Class) :
    Nominal.NPrf (.classEq (synCres A (synCvv)) A) :=
  by
  have p0000 := @gSsv (synCdm A)
  have p0001 := @gSsreseq A (synCvv)
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

/-- Checked nominal proof certificate identified upstream as `g_imadmrn`. -/
@[expose]
noncomputable def gImadmrn (A : Class) :
    Nominal.NPrf (.classEq (synCima A (synCdm A)) (synCrn A)) :=
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
  have dv_cache_0003 : y ∉ ((synCdm A)).fv :=
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
  have dv_cache_0004 : x ∉ ((synCdm A)).fv :=
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
  have p0000 := (Nominal.biimpRefl (synWrex x (synCdm A) (synWbr (.cv x) A (.cv y))))
  have p0001 := @gBreldm (.cv x) (.cv y) A
  have p0002 :=
    @gPm471ri (synWbr (.cv x) A (.cv y)) (.classMem (.cv x) (synCdm A)) p0001
  have p0003 :=
    @gExbii (synWbr (.cv x) A (.cv y))
      (synWa (.classMem (.cv x) (synCdm A)) (synWbr (.cv x) A (.cv y))) x p0002
  have p0004 :=
    @gBitr4i (synWrex x (synCdm A) (synWbr (.cv x) A (.cv y)))
      (synWex x (synWa (.classMem (.cv x) (synCdm A)) (synWbr (.cv x) A (.cv y))))
      (synWex x (synWbr (.cv x) A (.cv y))) p0000 p0003
  have p0005 :=
    @gAbbii (synWrex x (synCdm A) (synWbr (.cv x) A (.cv y)))
      (synWex x (synWbr (.cv x) A (.cv y))) y p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x A
      (synCdm A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 := @gDfrn2 x y A dv_cache_0002 dv_cache_0001 dv_cache_0006
  have p0008 :=
    @gN3eqtr4i (.cab y (synWrex x (synCdm A) (synWbr (.cv x) A (.cv y))))
      (.cab y (synWex x (synWbr (.cv x) A (.cv y)))) (synCima A (synCdm A))
      (synCrn A) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_imassrn`. -/
@[expose]
noncomputable def gImassrn (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCima A B) (synCrn A)) :=
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
  have p0000 := @gSimpr (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A)
  have p0001 :=
    @gEximi (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A))
      (.classMem (synCop (.cv x) (.cv y)) A) x p0000
  have p0002 :=
    @gSs2abi
      (synWex x (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A)))
      (synWex x (.classMem (synCop (.cv x) (.cv y)) A)) y p0001
  have p0003 :=
    @gDfima4 x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0004 := @gDfrn3 x y A dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0005 :=
    @gN3sstr4i
      (.cab y (synWex x
          (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A))))
      (.cab y (synWex x (.classMem (synCop (.cv x) (.cv y)) A))) (synCima A B)
      (synCrn A) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_imai`. -/
@[expose]
noncomputable def gImai (A : Class) : Nominal.NPrf (.classEq (synCima (synCid) A) A) :=
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
  have dv_cache_0001 : x ∉ ((synCid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCid)).fv :=
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
    @gDfima4 x y (synCid) A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) (synCid) (.cv y)))
  have p0002 := @gVex y
  have p0003 := @gIdeq (.cv x) (.cv y) p0002
  have p0004 :=
    @gBitr3i (.classMem (synCop (.cv x) (.cv y)) (synCid))
      (synWbr (.cv x) (synCid) (.cv y)) (.classEq (.cv x) (.cv y)) p0001 p0003
  have p0005 :=
    @gAnbi2i (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.classEq (.cv x) (.cv y))
      (.classMem (.cv x) A) p0004
  have p0006 := @gAncom (.classMem (.cv x) A) (.classEq (.cv x) (.cv y))
  have p0007 :=
    @gBitri
      (synWa (.classMem (.cv x) A) (.classMem (synCop (.cv x) (.cv y)) (synCid)))
      (synWa (.classMem (.cv x) A) (.classEq (.cv x) (.cv y)))
      (synWa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)) p0005 p0006
  have p0008 :=
    @gExbii
      (synWa (.classMem (.cv x) A) (.classMem (synCop (.cv x) (.cv y)) (synCid)))
      (synWa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)) x p0007
  have p0009 := @gEleq1 (.cv x) (.cv y) A
  have p0010 :=
    @gCeqsexv (.classMem (.cv x) A) (.classMem (.cv y) A) x (.cv y) dv_cache_0006
      dv_cache_0007 p0002 p0009
  have p0011 :=
    @gBitri
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (synCop (.cv x) (.cv y)) (synCid))))
      (synWex x (synWa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)))
      (.classMem (.cv y) A) p0008 p0010
  have p0012 :=
    @gAbbii
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (synCop (.cv x) (.cv y)) (synCid))))
      (.classMem (.cv y) A) y p0011
  have p0013 := @gAbid2 y A dv_cache_0004
  have p0014 :=
    @gN3eqtri (synCima (synCid) A)
      (.cab y (synWex x
          (synWa (.classMem (.cv x) A) (.classMem (synCop (.cv x) (.cv y)) (synCid)))))
      (.cab y (.classMem (.cv y) A)) A p0000 p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_ima0`. -/
@[expose]
noncomputable def gIma0 (A : Class) :
    Nominal.NPrf (.classEq (synCima A (synC0)) (synC0)) :=
  by
  have p0000 := @gDfima3 A (synC0)
  have p0001 := @gRes0 A
  have p0002 := @gRneqi (synCres A (synC0)) (synC0) p0001
  have p0003 := @gRn0
  have p0004 :=
    @gN3eqtri (synCima A (synC0)) (synCrn (synCres A (synC0))) (synCrn (synC0))
      (synC0) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cnvimass`. -/
@[expose]
noncomputable def gCnvimass (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCima (synCcnv A) B) (synCdm A)) :=
  by
  have p0000 := @gImassrn (synCcnv A) B
  have p0001 := (Nominal.classEqRefl (synCdm A))
  have p0002 :=
    @gSseqtr4i (synCima (synCcnv A) B) (synCrn (synCcnv A)) (synCdm A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_imasn`. -/
@[expose]
noncomputable def gImasn (y : Var) (A : Class) (R : Class) (dv_A_y : y ∉ A.fv)
    (dv_R_y : y ∉ R.fv) :
    Nominal.NPrf (.classEq (synCima R (synCsn A)) (.cab y (synWbr A R (.cv y)))) :=
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
  have dv_cache_0003 : y ∉ ((synCsn A)).fv :=
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
  have dv_cache_0004 : x ∉ ((synCsn A)).fv :=
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
  have dv_cache_0007 : x ∉ ((synWbr A R (.cv y))).fv :=
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
  have dv_cache_0008 : y ∉ ((Wff.classMem A (synCvv))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x R
      (synCsn A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gBreq1 (.cv x) A (.cv y) R
  have p0002 :=
    @gRexsng (synWbr (.cv x) R (.cv y)) (synWbr A R (.cv y)) x A (synCvv)
      dv_cache_0006 dv_cache_0007 p0001
  have p0003 :=
    @gAbbidv (.classMem A (synCvv)) (synWrex x (synCsn A) (synWbr (.cv x) R (.cv y)))
      (synWbr A R (.cv y)) y dv_cache_0008 p0002
  have p0004 :=
    @gSyl5eq (.classMem A (synCvv)) (synCima R (synCsn A))
      (.cab y (synWrex x (synCsn A) (synWbr (.cv x) R (.cv y))))
      (.cab y (synWbr A R (.cv y))) p0000 p0003
  have p0005 := @gIma0 R
  have p0006 := @gSnprc A
  have p0007 :=
    @gBiimpi (.neg (.classMem A (synCvv))) (.classEq (synCsn A) (synC0)) p0006
  have p0008 := @gImaeq2d (.neg (.classMem A (synCvv))) (synCsn A) (synC0) R p0007
  have p0009 := @gBrex A (.cv y) R
  have p0010 :=
    @gSimpld (synWbr A R (.cv y)) (.classMem A (synCvv)) (.classMem (.cv y) (synCvv))
      p0009
  have p0011 :=
    @gExlimiv (synWbr A R (.cv y)) (.classMem A (synCvv)) y dv_cache_0008 p0010
  have p0012 := @gCon3i (synWex y (synWbr A R (.cv y))) (.classMem A (synCvv)) p0011
  have p0013 := @gAbn0 (synWbr A R (.cv y)) y
  have p0014 := (Nominal.biimpRefl (synWne (.cab y (synWbr A R (.cv y))) (synC0)))
  have p0015 :=
    @gBitr3i (synWex y (synWbr A R (.cv y)))
      (synWne (.cab y (synWbr A R (.cv y))) (synC0))
      (.neg (.classEq (.cab y (synWbr A R (.cv y))) (synC0))) p0013 p0014
  have p0016 :=
    @gCon2bii (synWex y (synWbr A R (.cv y)))
      (.classEq (.cab y (synWbr A R (.cv y))) (synC0)) p0015
  have p0017 :=
    @gSylibr (.neg (.classMem A (synCvv))) (.neg (synWex y (synWbr A R (.cv y))))
      (.classEq (.cab y (synWbr A R (.cv y))) (synC0)) p0012 p0016
  have p0018 :=
    @gN3eqtr4a (.neg (.classMem A (synCvv))) (synCima R (synC0)) (synC0)
      (synCima R (synCsn A)) (.cab y (synWbr A R (.cv y))) p0005 p0008 p0017
  have p0019 :=
    @gPm261i (.classMem A (synCvv))
      (.classEq (synCima R (synCsn A)) (.cab y (synWbr A R (.cv y)))) p0004 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_elimasn`. -/
@[expose]
noncomputable def gElimasn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem C (synCima A (synCsn B))) (.classMem (synCop B C) A)) :=
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
  have dv_cache_0002 : x ∉ ((synWbr B A C)).fv :=
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
  have p0000 := @gElex C (synCima A (synCsn B))
  have p0001 := (Nominal.biimpRefl (synWbr B A C))
  have p0002 := @gBrex B C A
  have p0003 :=
    @gSimprd (synWbr B A C) (.classMem B (synCvv)) (.classMem C (synCvv)) p0002
  have p0004 :=
    @gSylbir (.classMem (synCop B C) A) (synWbr B A C) (.classMem C (synCvv)) p0001
      p0003
  have p0005 := @gBreq2 (.cv x) C B A
  have p0006 :=
    @gElabg (synWbr B A (.cv x)) (synWbr B A C) x C (synCvv) dv_cache_0001
      dv_cache_0002 p0005
  have p0007 := @gImasn x B A dv_cache_0003 dv_cache_0004
  have p0008 := @gEleq2i (synCima A (synCsn B)) (.cab x (synWbr B A (.cv x))) C p0007
  have p0009 := @gBicomi (synWbr B A C) (.classMem (synCop B C) A) p0001
  have p0010 :=
    @gN3bitr4g (.classMem C (synCvv)) (.classMem C (.cab x (synWbr B A (.cv x))))
      (synWbr B A C) (.classMem C (synCima A (synCsn B))) (.classMem (synCop B C) A)
      p0006 p0008 p0009
  have p0011 :=
    @gPm521nii (.classMem C (synCima A (synCsn B))) (.classMem C (synCvv))
      (.classMem (synCop B C) A) p0000 p0004 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_eliniseg`. -/
@[expose]
noncomputable def gEliniseg (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem C (synCima (synCcnv A) (synCsn B))) (synWbr C A B)) :=
  by
  have p0000 := @gElimasn (synCcnv A) B C
  have p0001 := (Nominal.biimpRefl (synWbr B (synCcnv A) C))
  have p0002 := @gBrcnv B C A
  have p0003 :=
    @gN3bitr2i (.classMem C (synCima (synCcnv A) (synCsn B)))
      (.classMem (synCop B C) (synCcnv A)) (synWbr B (synCcnv A) C) (synWbr C A B)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_iniseg`. -/
@[expose]
noncomputable def gIniseg (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.classEq (synCima (synCcnv A) (synCsn B)) (.cab x (synWbr (.cv x) A B))) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCcnv A)).fv :=
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
  have p0000 := @gImasn x B (synCcnv A) dv_cache_0001 dv_cache_0002
  have p0001 := @gBrcnv B (.cv x) A
  have p0002 := @gAbbii (synWbr B (synCcnv A) (.cv x)) (synWbr (.cv x) A B) x p0001
  have p0003 :=
    @gEqtri (synCima (synCcnv A) (synCsn B)) (.cab x (synWbr B (synCcnv A) (.cv x)))
      (.cab x (synWbr (.cv x) A B)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_imass2`. -/
@[expose]
noncomputable def gImass2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCima C A) (synCima C B))) :=
  by
  have p0000 := @gSsres2 A B C
  have p0001 := @gRnss (synCres C A) (synCres C B)
  have p0002 :=
    @gSyl (synWss A B) (synWss (synCres C A) (synCres C B))
      (synWss (synCrn (synCres C A)) (synCrn (synCres C B))) p0000 p0001
  have p0003 := @gDfima3 C A
  have p0004 := @gDfima3 C B
  have p0005 :=
    @gN3sstr4g (synWss A B) (synCrn (synCres C A)) (synCrn (synCres C B))
      (synCima C A) (synCima C B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ndmima`. -/
@[expose]
noncomputable def gNdmima (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A (synCdm B))) (.classEq (synCima B (synCsn A)) (synC0))) :=
  by
  have p0000 := @gDfima3 B (synCsn A)
  have p0001 := @gDmres B (synCsn A)
  have p0002 := @gIncom (synCsn A) (synCdm B)
  have p0003 :=
    @gEqtri (synCdm (synCres B (synCsn A))) (synCin (synCsn A) (synCdm B))
      (synCin (synCdm B) (synCsn A)) p0001 p0002
  have p0004 := @gDisjsn (synCdm B) A
  have p0005 :=
    @gBiimpri (.classEq (synCin (synCdm B) (synCsn A)) (synC0))
      (.neg (.classMem A (synCdm B))) p0004
  have p0006 :=
    @gSyl5eq (.neg (.classMem A (synCdm B))) (synCdm (synCres B (synCsn A)))
      (synCin (synCdm B) (synCsn A)) (synC0) p0003 p0005
  have p0007 := @gDm0rn0 (synCres B (synCsn A))
  have p0008 :=
    @gSylib (.neg (.classMem A (synCdm B)))
      (.classEq (synCdm (synCres B (synCsn A))) (synC0))
      (.classEq (synCrn (synCres B (synCsn A))) (synC0)) p0006 p0007
  have p0009 :=
    @gSyl5eq (.neg (.classMem A (synCdm B))) (synCima B (synCsn A))
      (synCrn (synCres B (synCsn A))) (synC0) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_cnvopab`. -/
@[expose]
noncomputable def gCnvopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (synCcnv (synCopab x y ph)) (synCopab y x ph)) :=
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
  have dv_cache_0005 : z ∉ ((synCcnv (synCopab x y ph))).fv :=
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
  have dv_cache_0006 : w ∉ ((synCcnv (synCopab x y ph))).fv :=
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
  have dv_cache_0007 : z ∉ ((synCopab y x ph)).fv :=
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
  have dv_cache_0008 : w ∉ ((synCopab y x ph)).fv :=
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
  have p0000 := @gOpelopabsb ph x y (.cv w) (.cv z) dv_cache_0001 dv_cache_0002
  have p0001 := @gSbccom ph x y (.cv w) (.cv z) dv_cache_0003 dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gBitri (.classMem (synCop (.cv w) (.cv z)) (synCopab x y ph))
      (synWsbc (.cv w) x (synWsbc (.cv z) y ph))
      (synWsbc (.cv z) y (synWsbc (.cv w) x ph)) p0000 p0001
  have p0003 := @gOpelcnv (.cv z) (.cv w) (synCopab x y ph)
  have p0004 := @gOpelopabsb ph y x (.cv z) (.cv w) dv_cache_0003 dv_cache_0004
  have p0005 :=
    @gN3bitr4i (.classMem (synCop (.cv w) (.cv z)) (synCopab x y ph))
      (synWsbc (.cv z) y (synWsbc (.cv w) x ph))
      (.classMem (synCop (.cv z) (.cv w)) (synCcnv (synCopab x y ph)))
      (.classMem (synCop (.cv z) (.cv w)) (synCopab y x ph)) p0002 p0003 p0004
  have p0006 :=
    @gEqrelriv z w (synCcnv (synCopab x y ph)) (synCopab y x ph) dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cnv0`. -/
@[expose]
noncomputable def gCnv0 : Nominal.NPrf (.classEq (synCcnv (synC0)) (synC0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((synCcnv (synC0))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCcnv (synC0))).fv :=
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
  have dv_cache_0003 : x ∉ ((synC0)).fv :=
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
  have dv_cache_0004 : y ∉ ((synC0)).fv :=
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
  have p0000 := @gNoel (synCop (.cv y) (.cv x))
  have p0001 := @gOpelcnv (.cv x) (.cv y) (synC0)
  have p0002 :=
    @gMtbir (.classMem (synCop (.cv x) (.cv y)) (synCcnv (synC0)))
      (.classMem (synCop (.cv y) (.cv x)) (synC0)) p0000 p0001
  have p0003 := @gNoel (synCop (.cv x) (.cv y))
  have p0004 :=
    @gN2false (.classMem (synCop (.cv x) (.cv y)) (synCcnv (synC0)))
      (.classMem (synCop (.cv x) (.cv y)) (synC0)) p0002 p0003
  have p0005 :=
    @gEqrelriv x y (synCcnv (synC0)) (synC0) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cnvi`. -/
@[expose]
noncomputable def gCnvi : Nominal.NPrf (.classEq (synCcnv (synCid)) (synCid)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((synCid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCid)).fv :=
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
  have p0000 := @gVex x
  have p0001 := @gIdeq (.cv y) (.cv x) p0000
  have p0002 := @gEqucom y x
  have p0003_e01_recanon :
    Nominal.NPrf (synWb (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gBitri (synWbr (.cv y) (synCid) (.cv x)) (.classEq (.cv y) (.cv x))
      (.classEq (.cv x) (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @gOpabbii (synWbr (.cv y) (synCid) (.cv x)) (.classEq (.cv x) (.cv y)) x y p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y (synCid)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfId x y dv_cache_0003
  have p0007_e02_recanon :
    Nominal.NPrf (.classEq (synCid) (synCopab x y (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCid synCopab synWex
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
    @gN3eqtr4i (synCopab x y (synWbr (.cv y) (synCid) (.cv x)))
      (synCopab x y (.classEq (.cv x) (.cv y))) (synCcnv (synCid)) (synCid) p0004
      p0005 p0007_e02_recanon
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_cnvun`. -/
@[expose]
noncomputable def gCnvun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCun A B)) (synCun (synCcnv A) (synCcnv B))) :=
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
  have dv_cache_0006 : x ∉ ((synCun A B)).fv :=
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
  have dv_cache_0007 : y ∉ ((synCun A B)).fv :=
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
  have p0000 := @gUnopab (synWbr (.cv y) A (.cv x)) (synWbr (.cv y) B (.cv x)) x y
  have p0001 := @gBrun (.cv y) (.cv x) A B
  have p0002 :=
    @gOpabbii (synWbr (.cv y) (synCun A B) (.cv x))
      (synWo (synWbr (.cv y) A (.cv x)) (synWbr (.cv y) B (.cv x))) x y p0001
  have p0003 :=
    @gEqtr4i
      (synCun (synCopab x y (synWbr (.cv y) A (.cv x)))
        (synCopab x y (synWbr (.cv y) B (.cv x))))
      (synCopab x y (synWo (synWbr (.cv y) A (.cv x)) (synWbr (.cv y) B (.cv x))))
      (synCopab x y (synWbr (.cv y) (synCun A B) (.cv x))) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y B
      dv_cache_0004 dv_cache_0005 dv_cache_0003
  have p0006 :=
    @gUneq12i (synCcnv A) (synCopab x y (synWbr (.cv y) A (.cv x))) (synCcnv B)
      (synCopab x y (synWbr (.cv y) B (.cv x))) p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y
      (synCun A B) dv_cache_0006 dv_cache_0007 dv_cache_0003
  have p0008 :=
    @gN3eqtr4ri
      (synCun (synCopab x y (synWbr (.cv y) A (.cv x)))
        (synCopab x y (synWbr (.cv y) B (.cv x))))
      (synCopab x y (synWbr (.cv y) (synCun A B) (.cv x)))
      (synCun (synCcnv A) (synCcnv B)) (synCcnv (synCun A B)) p0003 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_cnvdif`. -/
@[expose]
noncomputable def gCnvdif (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCdif A B)) (synCdif (synCcnv A) (synCcnv B))) :=
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
  have dv_cache_0001 : x ∉ ((synCcnv (synCdif A B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCcnv (synCdif A B))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCdif (synCcnv A) (synCcnv B))).fv :=
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
  have dv_cache_0004 : y ∉ ((synCdif (synCcnv A) (synCcnv B))).fv :=
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
  have p0000 := @gEldif (synCop (.cv y) (.cv x)) A B
  have p0001 := @gOpelcnv (.cv x) (.cv y) A
  have p0002 := @gOpelcnv (.cv x) (.cv y) B
  have p0003 :=
    @gNotbii (.classMem (synCop (.cv x) (.cv y)) (synCcnv B))
      (.classMem (synCop (.cv y) (.cv x)) B) p0002
  have p0004 :=
    @gAnbi12i (.classMem (synCop (.cv x) (.cv y)) (synCcnv A))
      (.classMem (synCop (.cv y) (.cv x)) A)
      (.neg (.classMem (synCop (.cv x) (.cv y)) (synCcnv B)))
      (.neg (.classMem (synCop (.cv y) (.cv x)) B)) p0001 p0003
  have p0005 :=
    @gBitr4i (.classMem (synCop (.cv y) (.cv x)) (synCdif A B))
      (synWa (.classMem (synCop (.cv y) (.cv x)) A)
        (.neg (.classMem (synCop (.cv y) (.cv x)) B)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCcnv A))
        (.neg (.classMem (synCop (.cv x) (.cv y)) (synCcnv B))))
      p0000 p0004
  have p0006 := @gOpelcnv (.cv x) (.cv y) (synCdif A B)
  have p0007 := @gEldif (synCop (.cv x) (.cv y)) (synCcnv A) (synCcnv B)
  have p0008 :=
    @gN3bitr4i (.classMem (synCop (.cv y) (.cv x)) (synCdif A B))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCcnv A))
        (.neg (.classMem (synCop (.cv x) (.cv y)) (synCcnv B))))
      (.classMem (synCop (.cv x) (.cv y)) (synCcnv (synCdif A B)))
      (.classMem (synCop (.cv x) (.cv y)) (synCdif (synCcnv A) (synCcnv B))) p0005
      p0006 p0007
  have p0009 :=
    @gEqrelriv x y (synCcnv (synCdif A B)) (synCdif (synCcnv A) (synCcnv B))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_cnvin`. -/
@[expose]
noncomputable def gCnvin (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCin A B)) (synCin (synCcnv A) (synCcnv B))) :=
  by
  have p0000 := @gCnvdif A (synCdif A B)
  have p0001 := @gCnvdif A B
  have p0002 :=
    @gDifeq2i (synCcnv (synCdif A B)) (synCdif (synCcnv A) (synCcnv B)) (synCcnv A)
      p0001
  have p0003 :=
    @gEqtri (synCcnv (synCdif A (synCdif A B)))
      (synCdif (synCcnv A) (synCcnv (synCdif A B)))
      (synCdif (synCcnv A) (synCdif (synCcnv A) (synCcnv B))) p0000 p0002
  have p0004 := @gDfin4 A B
  have p0005 := @gCnveqi (synCin A B) (synCdif A (synCdif A B)) p0004
  have p0006 := @gDfin4 (synCcnv A) (synCcnv B)
  have p0007 :=
    @gN3eqtr4i (synCcnv (synCdif A (synCdif A B)))
      (synCdif (synCcnv A) (synCdif (synCcnv A) (synCcnv B)))
      (synCcnv (synCin A B)) (synCin (synCcnv A) (synCcnv B)) p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_rnun`. -/
@[expose]
noncomputable def gRnun (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCrn (synCun A B)) (synCun (synCrn A) (synCrn B))) :=
  by
  have p0000 := @gCnvun A B
  have p0001 :=
    @gDmeqi (synCcnv (synCun A B)) (synCun (synCcnv A) (synCcnv B)) p0000
  have p0002 := @gDmun (synCcnv A) (synCcnv B)
  have p0003 :=
    @gEqtri (synCdm (synCcnv (synCun A B)))
      (synCdm (synCun (synCcnv A) (synCcnv B)))
      (synCun (synCdm (synCcnv A)) (synCdm (synCcnv B))) p0001 p0002
  have p0004 := @gDfrn4 (synCun A B)
  have p0005 := @gDfrn4 A
  have p0006 := @gDfrn4 B
  have p0007 :=
    @gUneq12i (synCrn A) (synCdm (synCcnv A)) (synCrn B) (synCdm (synCcnv B)) p0005
      p0006
  have p0008 :=
    @gN3eqtr4i (synCdm (synCcnv (synCun A B)))
      (synCun (synCdm (synCcnv A)) (synCdm (synCcnv B))) (synCrn (synCun A B))
      (synCun (synCrn A) (synCrn B)) p0003 p0004 p0007
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

/-- Checked nominal proof certificate identified upstream as `g_rnuni`. -/
@[expose]
noncomputable def gRnuni (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCrn (synCuni A)) (synCiun x A (synCrn (.cv x)))) :=
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
  have dv_cache_0001 : x ∉ ((synCop (.cv y) (.cv z))).fv := by
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
  have dv_cache_0006 : y ∉ ((synCuni A)).fv :=
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
  have dv_cache_0008 : z ∉ ((synCrn (synCuni A))).fv :=
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
  have dv_cache_0009 : z ∉ ((synCiun x A (synCrn (.cv x)))).fv :=
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
  have p0000 := @gEluni x (synCop (.cv y) (.cv z)) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gExbii (.classMem (synCop (.cv y) (.cv z)) (synCuni A))
      (synWex x (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      y p0000
  have p0002 :=
    @gExcom (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))
      y x
  have p0003 := @gElrn2 y (.cv z) (.cv x) dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gAnbi1i (.classMem (.cv z) (synCrn (.cv x)))
      (synWex y (.classMem (synCop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)
      p0003
  have p0005 := @gAncom (.classMem (.cv x) A) (.classMem (.cv z) (synCrn (.cv x)))
  have p0006 :=
    @gN1941v (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A) y
      dv_cache_0005
  have p0007 :=
    @gN3bitr4ri (synWa (.classMem (.cv z) (synCrn (.cv x))) (.classMem (.cv x) A))
      (synWa (synWex y (.classMem (synCop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) A) (.classMem (.cv z) (synCrn (.cv x))))
      (synWex y (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      p0004 p0005 p0006
  have p0008 :=
    @gExbii
      (synWex y (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv z) (synCrn (.cv x)))) x p0007
  have p0009 :=
    @gN3bitri (synWex y (.classMem (synCop (.cv y) (.cv z)) (synCuni A)))
      (synWex y (synWex x
          (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (synWex x (synWex y
          (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (.cv z) (synCrn (.cv x)))))
      p0001 p0002 p0008
  have p0010 := (Nominal.biimpRefl (synWrex x A (.classMem (.cv z) (synCrn (.cv x)))))
  have p0011 :=
    @gBitr4i (synWex y (.classMem (synCop (.cv y) (.cv z)) (synCuni A)))
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (.cv z) (synCrn (.cv x)))))
      (synWrex x A (.classMem (.cv z) (synCrn (.cv x)))) p0009 p0010
  have p0012 := @gElrn2 y (.cv z) (synCuni A) dv_cache_0003 dv_cache_0006
  have p0013 := @gEliun x (.cv z) A (synCrn (.cv x)) dv_cache_0007
  have p0014 :=
    @gN3bitr4i (synWex y (.classMem (synCop (.cv y) (.cv z)) (synCuni A)))
      (synWrex x A (.classMem (.cv z) (synCrn (.cv x))))
      (.classMem (.cv z) (synCrn (synCuni A)))
      (.classMem (.cv z) (synCiun x A (synCrn (.cv x)))) p0011 p0012 p0013
  have p0015 :=
    @gEqriv z (synCrn (synCuni A)) (synCiun x A (synCrn (.cv x))) dv_cache_0008
      dv_cache_0009 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_imaundi`. -/
@[expose]
noncomputable def gImaundi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCima A (synCun B C)) (synCun (synCima A B) (synCima A C))) :=
  by
  have p0000 := @gResundi A B C
  have p0001 :=
    @gRneqi (synCres A (synCun B C)) (synCun (synCres A B) (synCres A C)) p0000
  have p0002 := @gRnun (synCres A B) (synCres A C)
  have p0003 :=
    @gEqtri (synCrn (synCres A (synCun B C)))
      (synCrn (synCun (synCres A B) (synCres A C)))
      (synCun (synCrn (synCres A B)) (synCrn (synCres A C))) p0001 p0002
  have p0004 := @gDfima3 A (synCun B C)
  have p0005 := @gDfima3 A B
  have p0006 := @gDfima3 A C
  have p0007 :=
    @gUneq12i (synCima A B) (synCrn (synCres A B)) (synCima A C)
      (synCrn (synCres A C)) p0005 p0006
  have p0008 :=
    @gN3eqtr4i (synCrn (synCres A (synCun B C)))
      (synCun (synCrn (synCres A B)) (synCrn (synCres A C)))
      (synCima A (synCun B C)) (synCun (synCima A B) (synCima A C)) p0003 p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_imaundir`. -/
@[expose]
noncomputable def gImaundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCima (synCun A B) C) (synCun (synCima A C) (synCima B C))) :=
  by
  have p0000 := @gDfima3 (synCun A B) C
  have p0001 := @gResundir A B C
  have p0002 :=
    @gRneqi (synCres (synCun A B) C) (synCun (synCres A C) (synCres B C)) p0001
  have p0003 := @gRnun (synCres A C) (synCres B C)
  have p0004 :=
    @gN3eqtri (synCima (synCun A B) C) (synCrn (synCres (synCun A B) C))
      (synCrn (synCun (synCres A C) (synCres B C)))
      (synCun (synCrn (synCres A C)) (synCrn (synCres B C))) p0000 p0002 p0003
  have p0005 := @gDfima3 A C
  have p0006 := @gDfima3 B C
  have p0007 :=
    @gUneq12i (synCima A C) (synCrn (synCres A C)) (synCima B C)
      (synCrn (synCres B C)) p0005 p0006
  have p0008 :=
    @gEqtr4i (synCima (synCun A B) C)
      (synCun (synCrn (synCres A C)) (synCrn (synCres B C)))
      (synCun (synCima A C) (synCima B C)) p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_cnvxp`. -/
@[expose]
noncomputable def gCnvxp (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCcnv (synCxp A B)) (synCxp B A)) :=
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
    @gCnvopab (synWa (.classMem (.cv y) A) (.classMem (.cv x) B)) y x dv_cache_0001
  have p0001 := @gAncom (.classMem (.cv y) A) (.classMem (.cv x) B)
  have p0002 :=
    @gOpabbii (synWa (.classMem (.cv y) A) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) A)) x y p0001
  have p0003 :=
    @gEqtri
      (synCcnv (synCopab y x (synWa (.classMem (.cv y) A) (.classMem (.cv x) B))))
      (synCopab x y (synWa (.classMem (.cv y) A) (.classMem (.cv x) B)))
      (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) A))) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp y x A B
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
  have p0005 :=
    @gCnveqi (synCxp A B)
      (synCopab y x (synWa (.classMem (.cv y) A) (.classMem (.cv x) B))) p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y B A
      dv_cache_0005 dv_cache_0004 dv_cache_0003 dv_cache_0002 dv_cache_0006
  have p0007 :=
    @gN3eqtr4i
      (synCcnv (synCopab y x (synWa (.classMem (.cv y) A) (.classMem (.cv x) B))))
      (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) A)))
      (synCcnv (synCxp A B)) (synCxp B A) p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_xp0`. -/
@[expose]
noncomputable def gXp0 (A : Class) :
    Nominal.NPrf (.classEq (synCxp A (synC0)) (synC0)) :=
  by
  have p0000 := @gXp0r A
  have p0001 := @gCnveqi (synCxp (synC0) A) (synC0) p0000
  have p0002 := @gCnvxp (synC0) A
  have p0003 := @gCnv0
  have p0004 :=
    @gN3eqtr3i (synCcnv (synCxp (synC0) A)) (synCcnv (synC0)) (synCxp A (synC0))
      (synC0) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_xpdisj2`. -/
@[expose]
noncomputable def gXpdisj2 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (.classEq (synCin A B) (synC0))
        (.classEq (synCin (synCxp C A) (synCxp D B)) (synC0))) :=
  by
  have p0000 := @gInxp C A D B
  have p0001 := @gXpeq2 (synCin A B) (synC0) (synCin C D)
  have p0002 := @gXp0 (synCin C D)
  have p0003 :=
    @gSyl6eq (.classEq (synCin A B) (synC0)) (synCxp (synCin C D) (synCin A B))
      (synCxp (synCin C D) (synC0)) (synC0) p0001 p0002
  have p0004 :=
    @gSyl5eq (.classEq (synCin A B) (synC0)) (synCin (synCxp C A) (synCxp D B))
      (synCxp (synCin C D) (synCin A B)) (synC0) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dmxpss`. -/
@[expose]
noncomputable def gDmxpss (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCdm (synCxp A B)) A) :=
  by
  have p0000 := @gN0ss A
  have p0001 := @gXpeq2 B (synC0) A
  have p0002 := @gXp0 A
  have p0003 :=
    @gSyl6eq (.classEq B (synC0)) (synCxp A B) (synCxp A (synC0)) (synC0) p0001
      p0002
  have p0004 := @gDmeqd (.classEq B (synC0)) (synCxp A B) (synC0) p0003
  have p0005 := @gDm0
  have p0006 :=
    @gSyl6eq (.classEq B (synC0)) (synCdm (synCxp A B)) (synCdm (synC0)) (synC0)
      p0004 p0005
  have p0007 := @gSseq1d (.classEq B (synC0)) (synCdm (synCxp A B)) (synC0) A p0006
  have p0008 :=
    @gMpbiri (.classEq B (synC0)) (synWss (synCdm (synCxp A B)) A)
      (synWss (synC0) A) p0000 p0007
  have p0009 := @gDmxp A B
  have p0010 := @gEqimss (synCdm (synCxp A B)) A
  have p0011 :=
    @gSyl (synWne B (synC0)) (.classEq (synCdm (synCxp A B)) A)
      (synWss (synCdm (synCxp A B)) A) p0009 p0010
  have p0012 := @gPm261ine (synWss (synCdm (synCxp A B)) A) B (synC0) p0008 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_rnxpss`. -/
@[expose]
noncomputable def gRnxpss (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCrn (synCxp A B)) B) :=
  by
  have p0000 := @gDfrn4 (synCxp A B)
  have p0001 := @gCnvxp A B
  have p0002 := @gDmeqi (synCcnv (synCxp A B)) (synCxp B A) p0001
  have p0003 :=
    @gEqtri (synCrn (synCxp A B)) (synCdm (synCcnv (synCxp A B)))
      (synCdm (synCxp B A)) p0000 p0002
  have p0004 := @gDmxpss B A
  have p0005 := @gEqsstri (synCrn (synCxp A B)) (synCdm (synCxp B A)) B p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cnvcnv`. -/
@[expose]
noncomputable def gCnvcnv (R : Class) :
    Nominal.NPrf (.classEq (synCcnv (synCcnv R)) R) :=
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
  have dv_cache_0001 : x ∉ ((synCcnv (synCcnv R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCcnv (synCcnv R))).fv :=
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
  have p0000 := @gBrcnv (.cv x) (.cv y) (synCcnv R)
  have p0001 := @gBrcnv (.cv y) (.cv x) R
  have p0002 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCcnv R)) (.cv y))
      (synWbr (.cv y) (synCcnv R) (.cv x)) (synWbr (.cv x) R (.cv y)) p0000 p0001
  have p0003 :=
    @gEqbrriv x y (synCcnv (synCcnv R)) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cnveqb`. -/
@[expose]
noncomputable def gCnveqb (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classEq A B) (.classEq (synCcnv A) (synCcnv B))) :=
  by
  have p0000 := @gCnveq A B
  have p0001 := @gCnveq (synCcnv A) (synCcnv B)
  have p0002 := @gCnvcnv A
  have p0003 := @gCnvcnv B
  have p0004 :=
    @gN3eqtr3g (.classEq (synCcnv A) (synCcnv B)) (synCcnv (synCcnv A))
      (synCcnv (synCcnv B)) A B p0001 p0002 p0003
  have p0005 := @gImpbii (.classEq A B) (.classEq (synCcnv A) (synCcnv B)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dmsnopg`. -/
@[expose]
noncomputable def gDmsnopg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem B V) (.classEq (synCdm (synCsn (synCop A B))) (synCsn A))) :=
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
  have dv_cache_0004 : z ∉ ((synCsn (synCop A (.cv y)))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCdm (synCsn (synCop A (.cv y))))).fv :=
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
  have dv_cache_0007 : x ∉ ((synCsn A)).fv :=
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
    y ∉ ((Wff.classEq (synCdm (synCsn (synCop A B))) (synCsn A))).fv :=
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
  have p0000 := @gOpeq2 (.cv y) B A
  have p0001 := @gSneqd (.classEq (.cv y) B) (synCop A (.cv y)) (synCop A B) p0000
  have p0002 :=
    @gDmeqd (.classEq (.cv y) B) (synCsn (synCop A (.cv y))) (synCsn (synCop A B))
      p0001
  have p0003 :=
    @gEqeq1d (.classEq (.cv y) B) (synCdm (synCsn (synCop A (.cv y))))
      (synCdm (synCsn (synCop A B))) (synCsn A) p0002
  have p0004 :=
    (Nominal.biimpRefl (synWbr (.cv x) (synCsn (synCop A (.cv y))) (.cv z)))
  have p0005 := @gVex x
  have p0006 := @gVex z
  have p0007 := @gOpex (.cv x) (.cv z) p0005 p0006
  have p0008 := @gElsnc (synCop (.cv x) (.cv z)) (synCop A (.cv y)) p0007
  have p0009 := @gOpth (.cv x) (.cv z) A (.cv y)
  have p0010 := @gAncom (.classEq (.cv x) A) (.objEq z y)
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv x) (.cv z)) (synCop A (.cv y)))
        (synWa (.classEq (.cv x) A) (.objEq z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gBitri (.classEq (synCop (.cv x) (.cv z)) (synCop A (.cv y)))
      (synWa (.classEq (.cv x) A) (.objEq z y))
      (synWa (.objEq z y) (.classEq (.cv x) A)) p0011_e00_recanon p0010
  have p0012 :=
    @gN3bitri (synWbr (.cv x) (synCsn (synCop A (.cv y))) (.cv z))
      (.classMem (synCop (.cv x) (.cv z)) (synCsn (synCop A (.cv y))))
      (.classEq (synCop (.cv x) (.cv z)) (synCop A (.cv y)))
      (synWa (.objEq z y) (.classEq (.cv x) A)) p0004 p0008 p0011
  have p0013 :=
    @gExbii (synWbr (.cv x) (synCsn (synCop A (.cv y))) (.cv z))
      (synWa (.objEq z y) (.classEq (.cv x) A)) z p0012
  have p0014 := @gVex y
  have p0015 := @gBiidd (.objEq z y) (.classEq (.cv x) A)
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y)) (synWb (.classEq (.cv x) A) (.classEq (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gCeqsexv (.classEq (.cv x) A) (.classEq (.cv x) A) z (.cv y) dv_cache_0001
      dv_cache_0002 p0014 p0016_e01_recanon
  have p0017_e01_recanon :
    Nominal.NPrf
      (synWb (synWex z (synWa (.objEq z y) (.classEq (.cv x) A))) (.classEq (.cv x) A)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa
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
    @gBitri (synWex z (synWbr (.cv x) (synCsn (synCop A (.cv y))) (.cv z)))
      (synWex z (synWa (.objEq z y) (.classEq (.cv x) A))) (.classEq (.cv x) A) p0013
      p0017_e01_recanon
  have p0018 :=
    @gEldm z (.cv x) (synCsn (synCop A (.cv y))) dv_cache_0003 dv_cache_0004
  have p0019 := @gElsn x A dv_cache_0005
  have p0020 :=
    @gN3bitr4i (synWex z (synWbr (.cv x) (synCsn (synCop A (.cv y))) (.cv z)))
      (.classEq (.cv x) A) (.classMem (.cv x) (synCdm (synCsn (synCop A (.cv y)))))
      (.classMem (.cv x) (synCsn A)) p0017 p0018 p0019
  have p0021 :=
    @gEqriv x (synCdm (synCsn (synCop A (.cv y)))) (synCsn A) dv_cache_0006
      dv_cache_0007 p0020
  have p0022 :=
    @gVtoclg (.classEq (synCdm (synCsn (synCop A (.cv y)))) (synCsn A))
      (.classEq (synCdm (synCsn (synCop A B))) (synCsn A)) y B V dv_cache_0008
      dv_cache_0009 p0003 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_dmsnop`. -/
@[expose]
noncomputable def gDmsnop (A : Class) (B : Class)
    (hyp_dmsnop_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCdm (synCsn (synCop A B))) (synCsn A)) :=
  by
  have p0000 := @gDmsnopg A B (synCvv)
  have p0001 := Nominal.mp hyp_dmsnop_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cnvsn`. -/
@[expose]
noncomputable def gCnvsn (A : Class) (B : Class)
    (_hyp_cnvsn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (_hyp_cnvsn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCcnv (synCsn (synCop A B))) (synCsn (synCop B A))) :=
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
  have dv_cache_0001 : x ∉ ((synCcnv (synCsn (synCop A B)))).fv := by
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
  have dv_cache_0002 : y ∉ ((synCcnv (synCsn (synCop A B)))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCsn (synCop B A))).fv :=
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
  have dv_cache_0004 : y ∉ ((synCsn (synCop B A))).fv :=
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
  have p0000 := @gVex y
  have p0001 := @gVex x
  have p0002 := @gOpex (.cv y) (.cv x) p0000 p0001
  have p0003 := @gElsnc (synCop (.cv y) (.cv x)) (synCop A B) p0002
  have p0004 := @gAncom (.classEq (.cv y) A) (.classEq (.cv x) B)
  have p0005 := @gOpth (.cv y) (.cv x) A B
  have p0006 := @gOpth (.cv x) (.cv y) B A
  have p0007 :=
    @gN3bitr4i (synWa (.classEq (.cv y) A) (.classEq (.cv x) B))
      (synWa (.classEq (.cv x) B) (.classEq (.cv y) A))
      (.classEq (synCop (.cv y) (.cv x)) (synCop A B))
      (.classEq (synCop (.cv x) (.cv y)) (synCop B A)) p0004 p0005 p0006
  have p0008 :=
    @gBitri (.classMem (synCop (.cv y) (.cv x)) (synCsn (synCop A B)))
      (.classEq (synCop (.cv y) (.cv x)) (synCop A B))
      (.classEq (synCop (.cv x) (.cv y)) (synCop B A)) p0003 p0007
  have p0009 := @gOpelcnv (.cv x) (.cv y) (synCsn (synCop A B))
  have p0010 := @gOpex (.cv x) (.cv y) p0001 p0000
  have p0011 := @gElsnc (synCop (.cv x) (.cv y)) (synCop B A) p0010
  have p0012 :=
    @gN3bitr4i (.classMem (synCop (.cv y) (.cv x)) (synCsn (synCop A B)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop B A))
      (.classMem (synCop (.cv x) (.cv y)) (synCcnv (synCsn (synCop A B))))
      (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop B A))) p0008 p0009 p0011
  have p0013 :=
    @gEqrelriv x y (synCcnv (synCsn (synCop A B))) (synCsn (synCop B A))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_rnsnop`. -/
@[expose]
noncomputable def gRnsnop (A : Class) (B : Class)
    (hyp_rnsnop_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCrn (synCsn (synCop A B))) (synCsn B)) :=
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
  have dv_cache_0004 : x ∉ ((synCsn (synCop A B))).fv :=
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
  have dv_cache_0005 : y ∉ ((synCrn (synCsn (synCop A B)))).fv :=
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
  have dv_cache_0006 : y ∉ ((synCsn B)).fv :=
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
  have p0000 := (Nominal.biimpRefl (synWbr (.cv x) (synCsn (synCop A B)) (.cv y)))
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gOpex (.cv x) (.cv y) p0001 p0002
  have p0004 := @gElsnc (synCop (.cv x) (.cv y)) (synCop A B) p0003
  have p0005 := @gOpth (.cv x) (.cv y) A B
  have p0006 :=
    @gBitri (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop A B)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0004 p0005
  have p0007 :=
    @gBitri (synWbr (.cv x) (synCsn (synCop A B)) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop A B)))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0006
  have p0008 :=
    @gExbii (synWbr (.cv x) (synCsn (synCop A B)) (.cv y))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) x p0007
  have p0009 := @gBiidd (.classEq (.cv x) A) (.classEq (.cv y) B)
  have p0010 :=
    @gCeqsexv (.classEq (.cv y) B) (.classEq (.cv y) B) x A dv_cache_0001 dv_cache_0002
      hyp_rnsnop_1 p0009
  have p0011 :=
    @gBitri (synWex x (synWbr (.cv x) (synCsn (synCop A B)) (.cv y)))
      (synWex x (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))) (.classEq (.cv y) B)
      p0008 p0010
  have p0012 := @gElrn x (.cv y) (synCsn (synCop A B)) dv_cache_0003 dv_cache_0004
  have p0013 := @gElsnc (.cv y) B p0002
  have p0014 :=
    @gN3bitr4i (synWex x (synWbr (.cv x) (synCsn (synCop A B)) (.cv y)))
      (.classEq (.cv y) B) (.classMem (.cv y) (synCrn (synCsn (synCop A B))))
      (.classMem (.cv y) (synCsn B)) p0011 p0012 p0013
  have p0015 :=
    @gEqriv y (synCrn (synCsn (synCop A B))) (synCsn B) dv_cache_0005 dv_cache_0006
      p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_cnvresima`. -/
@[expose]
noncomputable def gCnvresima (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.classEq (synCima (synCcnv (synCres F A)) B) (synCin (synCima (synCcnv F) B) A)) :=
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
  have dv_cache_0002 : s ∉ ((synCcnv (synCres F A))).fv :=
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
  have dv_cache_0005 : s ∉ ((synCcnv F)).fv :=
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
  have dv_cache_0006 : t ∉ ((synCima (synCcnv (synCres F A)) B)).fv :=
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
  have dv_cache_0007 : t ∉ ((synCin (synCima (synCcnv F) B) A)).fv :=
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
    @gElima3 s (.cv t) (synCcnv (synCres F A)) B dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 :=
    @gAnass (.classMem (.cv s) B) (.classMem (synCop (.cv s) (.cv t)) (synCcnv F))
      (.classMem (.cv t) A)
  have p0002 := @gOpelres (.cv t) (.cv s) F A
  have p0003 := @gOpelcnv (.cv s) (.cv t) (synCres F A)
  have p0004 := @gOpelcnv (.cv s) (.cv t) F
  have p0005 :=
    @gAnbi1i (.classMem (synCop (.cv s) (.cv t)) (synCcnv F))
      (.classMem (synCop (.cv t) (.cv s)) F) (.classMem (.cv t) A) p0004
  have p0006 :=
    @gN3bitr4ri (.classMem (synCop (.cv t) (.cv s)) (synCres F A))
      (synWa (.classMem (synCop (.cv t) (.cv s)) F) (.classMem (.cv t) A))
      (.classMem (synCop (.cv s) (.cv t)) (synCcnv (synCres F A)))
      (synWa (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)) (.classMem (.cv t) A))
      p0002 p0003 p0005
  have p0007 :=
    @gAnbi2i
      (synWa (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)) (.classMem (.cv t) A))
      (.classMem (synCop (.cv s) (.cv t)) (synCcnv (synCres F A)))
      (.classMem (.cv s) B) p0006
  have p0008 :=
    @gBitr2i
      (synWa (synWa (.classMem (.cv s) B) (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)))
        (.classMem (.cv t) A))
      (synWa (.classMem (.cv s) B)
        (synWa (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)) (.classMem (.cv t) A)))
      (synWa (.classMem (.cv s) B)
        (.classMem (synCop (.cv s) (.cv t)) (synCcnv (synCres F A))))
      p0001 p0007
  have p0009 :=
    @gExbii
      (synWa (.classMem (.cv s) B)
        (.classMem (synCop (.cv s) (.cv t)) (synCcnv (synCres F A))))
      (synWa (synWa (.classMem (.cv s) B) (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)))
        (.classMem (.cv t) A))
      s p0008
  have p0010 :=
    @gN1941v
      (synWa (.classMem (.cv s) B) (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)))
      (.classMem (.cv t) A) s dv_cache_0004
  have p0011 :=
    @gBitri
      (synWex s (synWa (.classMem (.cv s) B)
          (.classMem (synCop (.cv s) (.cv t)) (synCcnv (synCres F A)))))
      (synWex s (synWa (synWa (.classMem (.cv s) B)
            (.classMem (synCop (.cv s) (.cv t)) (synCcnv F))) (.classMem (.cv t) A)))
      (synWa (synWex s (synWa (.classMem (.cv s) B)
            (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)))) (.classMem (.cv t) A))
      p0009 p0010
  have p0012 := @gElin (.cv t) (synCima (synCcnv F) B) A
  have p0013 :=
    @gElima3 s (.cv t) (synCcnv F) B dv_cache_0001 dv_cache_0005 dv_cache_0003
  have p0014 :=
    @gAnbi1i (.classMem (.cv t) (synCima (synCcnv F) B))
      (synWex s
        (synWa (.classMem (.cv s) B) (.classMem (synCop (.cv s) (.cv t)) (synCcnv F))))
      (.classMem (.cv t) A) p0013
  have p0015 :=
    @gBitr2i (.classMem (.cv t) (synCin (synCima (synCcnv F) B) A))
      (synWa (.classMem (.cv t) (synCima (synCcnv F) B)) (.classMem (.cv t) A))
      (synWa (synWex s (synWa (.classMem (.cv s) B)
            (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)))) (.classMem (.cv t) A))
      p0012 p0014
  have p0016 :=
    @gN3bitri (.classMem (.cv t) (synCima (synCcnv (synCres F A)) B))
      (synWex s (synWa (.classMem (.cv s) B)
          (.classMem (synCop (.cv s) (.cv t)) (synCcnv (synCres F A)))))
      (synWa (synWex s (synWa (.classMem (.cv s) B)
            (.classMem (synCop (.cv s) (.cv t)) (synCcnv F)))) (.classMem (.cv t) A))
      (.classMem (.cv t) (synCin (synCima (synCcnv F) B) A)) p0000 p0011 p0015
  have p0017 :=
    @gEqriv t (synCima (synCcnv (synCres F A)) B)
      (synCin (synCima (synCcnv F) B) A) dv_cache_0006 dv_cache_0007 p0016
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

/-- Checked nominal proof certificate identified upstream as `g_resco`. -/
@[expose]
noncomputable def gResco (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCres (synCcom A B) C) (synCcom A (synCres B C))) :=
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
  have dv_cache_0006 : z ∉ ((synCres B C)).fv :=
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
  have dv_cache_0007 : x ∉ ((synCres (synCcom A B) C)).fv :=
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
  have dv_cache_0008 : y ∉ ((synCres (synCcom A B) C)).fv :=
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
  have dv_cache_0009 : x ∉ ((synCcom A (synCres B C))).fv :=
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
  have dv_cache_0010 : y ∉ ((synCcom A (synCres B C))).fv :=
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
    @gBrco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @gAnbi1i (synWbr (.cv x) (synCcom A B) (.cv y))
      (synWex z (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y))))
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @gN1941v (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
      (.classMem (.cv x) C) z dv_cache_0005
  have p0003 :=
    @gAn32 (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)) (.classMem (.cv x) C)
  have p0004 := @gBrres (.cv x) (.cv z) B C
  have p0005 :=
    @gAnbi1i (synWbr (.cv x) (synCres B C) (.cv z))
      (synWa (synWbr (.cv x) B (.cv z)) (.classMem (.cv x) C))
      (synWbr (.cv z) A (.cv y)) p0004
  have p0006 :=
    @gBitr4i
      (synWa (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
        (.classMem (.cv x) C))
      (synWa (synWa (synWbr (.cv x) B (.cv z)) (.classMem (.cv x) C))
        (synWbr (.cv z) A (.cv y)))
      (synWa (synWbr (.cv x) (synCres B C) (.cv z)) (synWbr (.cv z) A (.cv y))) p0003
      p0005
  have p0007 :=
    @gExbii
      (synWa (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
        (.classMem (.cv x) C))
      (synWa (synWbr (.cv x) (synCres B C) (.cv z)) (synWbr (.cv z) A (.cv y))) z
      p0006
  have p0008 :=
    @gN3bitr2i (synWa (synWbr (.cv x) (synCcom A B) (.cv y)) (.classMem (.cv x) C))
      (synWa (synWex z (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y))))
        (.classMem (.cv x) C))
      (synWex z (synWa (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
          (.classMem (.cv x) C)))
      (synWex z (synWa (synWbr (.cv x) (synCres B C) (.cv z)) (synWbr (.cv z) A (.cv y))))
      p0001 p0002 p0007
  have p0009 := @gBrres (.cv x) (.cv y) (synCcom A B) C
  have p0010 :=
    @gBrco z (.cv x) (.cv y) A (synCres B C) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0006
  have p0011 :=
    @gN3bitr4i (synWa (synWbr (.cv x) (synCcom A B) (.cv y)) (.classMem (.cv x) C))
      (synWex z (synWa (synWbr (.cv x) (synCres B C) (.cv z)) (synWbr (.cv z) A (.cv y))))
      (synWbr (.cv x) (synCres (synCcom A B) C) (.cv y))
      (synWbr (.cv x) (synCcom A (synCres B C)) (.cv y)) p0008 p0009 p0010
  have p0012 :=
    @gEqbrriv x y (synCres (synCcom A B) C) (synCcom A (synCres B C)) dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_imaco`. -/
@[expose]
noncomputable def gImaco (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCima (synCcom A B) C) (synCima A (synCima B C))) :=
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
  have dv_cache_0003 : y ∉ ((synCima B C)).fv :=
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
  have dv_cache_0004 : z ∉ ((synWbr (.cv y) A (.cv x))).fv :=
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
  have dv_cache_0006 : z ∉ ((synCcom A B)).fv :=
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
  have dv_cache_0014 : x ∉ ((synCima (synCcom A B) C)).fv :=
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
  have dv_cache_0015 : x ∉ ((synCima A (synCima B C))).fv :=
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
    (Nominal.biimpRefl (synWrex y (synCima B C) (synWbr (.cv y) A (.cv x))))
  have p0001 :=
    @gElima y (.cv x) A (synCima B C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gR1941v (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x)) z C dv_cache_0004
  have p0003 :=
    @gExbii
      (synWrex z C (synWa (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x))))
      (synWa (synWrex z C (synWbr (.cv z) B (.cv y))) (synWbr (.cv y) A (.cv x))) y
      p0002
  have p0004 :=
    @gElima z (.cv x) (synCcom A B) C dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @gBrco y (.cv z) (.cv x) A B dv_cache_0008 dv_cache_0001 dv_cache_0002 dv_cache_0009
  have p0006 :=
    @gRexbii (synWbr (.cv z) (synCcom A B) (.cv x))
      (synWex y (synWa (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x)))) z C
      p0005
  have p0007 :=
    @gRexcom4 (synWa (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x))) z y C
      dv_cache_0010 dv_cache_0011
  have p0008 :=
    @gN3bitri (.classMem (.cv x) (synCima (synCcom A B) C))
      (synWrex z C (synWbr (.cv z) (synCcom A B) (.cv x)))
      (synWrex z C
        (synWex y (synWa (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x)))))
      (synWex y
        (synWrex z C (synWa (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x)))))
      p0004 p0006 p0007
  have p0009 := @gElima z (.cv y) B C dv_cache_0012 dv_cache_0013 dv_cache_0007
  have p0010 :=
    @gAnbi1i (.classMem (.cv y) (synCima B C))
      (synWrex z C (synWbr (.cv z) B (.cv y))) (synWbr (.cv y) A (.cv x)) p0009
  have p0011 :=
    @gExbii (synWa (.classMem (.cv y) (synCima B C)) (synWbr (.cv y) A (.cv x)))
      (synWa (synWrex z C (synWbr (.cv z) B (.cv y))) (synWbr (.cv y) A (.cv x))) y
      p0010
  have p0012 :=
    @gN3bitr4i
      (synWex y
        (synWrex z C (synWa (synWbr (.cv z) B (.cv y)) (synWbr (.cv y) A (.cv x)))))
      (synWex y
        (synWa (synWrex z C (synWbr (.cv z) B (.cv y))) (synWbr (.cv y) A (.cv x))))
      (.classMem (.cv x) (synCima (synCcom A B) C))
      (synWex y (synWa (.classMem (.cv y) (synCima B C)) (synWbr (.cv y) A (.cv x))))
      p0003 p0008 p0011
  have p0013 :=
    @gN3bitr4ri (synWrex y (synCima B C) (synWbr (.cv y) A (.cv x)))
      (synWex y (synWa (.classMem (.cv y) (synCima B C)) (synWbr (.cv y) A (.cv x))))
      (.classMem (.cv x) (synCima A (synCima B C)))
      (.classMem (.cv x) (synCima (synCcom A B) C)) p0000 p0001 p0012
  have p0014 :=
    @gEqriv x (synCima (synCcom A B) C) (synCima A (synCima B C)) dv_cache_0014
      dv_cache_0015 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_co01`. -/
@[expose]
noncomputable def gCo01 (A : Class) :
    Nominal.NPrf (.classEq (synCcom (synC0) A) (synC0)) :=
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
  have dv_cache_0001 : x ∉ ((synCcom (synC0) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCproj1 (.cv x))).fv :=
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
  have dv_cache_0003 : y ∉ ((synCproj2 (.cv x))).fv :=
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
  have dv_cache_0004 : y ∉ ((synC0)).fv :=
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
  have p0000 := @gEq0 x (synCcom (synC0) A) dv_cache_0001
  have p0001 := @gNoel (synCop (.cv y) (synCproj2 (.cv x)))
  have p0002 := (Nominal.biimpRefl (synWbr (.cv y) (synC0) (synCproj2 (.cv x))))
  have p0003 :=
    @gMtbir (synWbr (.cv y) (synC0) (synCproj2 (.cv x)))
      (.classMem (synCop (.cv y) (synCproj2 (.cv x))) (synC0)) p0001 p0002
  have p0004 :=
    @gIntnan (synWbr (.cv y) (synC0) (synCproj2 (.cv x)))
      (synWbr (synCproj1 (.cv x)) A (.cv y)) p0003
  have p0005 :=
    @gNex
      (synWa (synWbr (synCproj1 (.cv x)) A (.cv y))
        (synWbr (.cv y) (synC0) (synCproj2 (.cv x))))
      y p0004
  have p0006 := @gOpeq (.cv x)
  have p0007 :=
    @gEleq1i (.cv x) (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
      (synCcom (synC0) A) p0006
  have p0008 :=
    @gOpelco y (synCproj1 (.cv x)) (synCproj2 (.cv x)) (synC0) A dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    @gBitri (.classMem (.cv x) (synCcom (synC0) A))
      (.classMem (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x))) (synCcom (synC0) A))
      (synWex y (synWa (synWbr (synCproj1 (.cv x)) A (.cv y))
          (synWbr (.cv y) (synC0) (synCproj2 (.cv x)))))
      p0007 p0008
  have p0010 :=
    @gMtbir (.classMem (.cv x) (synCcom (synC0) A))
      (synWex y (synWa (synWbr (synCproj1 (.cv x)) A (.cv y))
          (synWbr (.cv y) (synC0) (synCproj2 (.cv x)))))
      p0005 p0009
  have p0011 :=
    @gMpgbir (.classEq (synCcom (synC0) A) (synC0))
      (.neg (.classMem (.cv x) (synCcom (synC0) A))) x p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_coi1`. -/
@[expose]
noncomputable def gCoi1 (A : Class) : Nominal.NPrf (.classEq (synCcom A (synCid)) A) :=
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
  have dv_cache_0004 : z ∉ ((synCid)).fv :=
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
  have dv_cache_0005 : z ∉ ((synWbr (.cv x) A (.cv y))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCcom A (synCid))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCcom A (synCid))).fv :=
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
    @gBrco z (.cv x) (.cv y) A (synCid) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @gVex z
  have p0002 := @gIdeq (.cv x) (.cv z) p0001
  have p0003 := @gEqucom x z
  have p0004_e00_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv z)) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
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
    @gBitri (synWbr (.cv x) (synCid) (.cv z)) (.objEq x z) (.objEq z x)
      p0004_e00_recanon p0003
  have p0005 :=
    @gAnbi1i (synWbr (.cv x) (synCid) (.cv z)) (.objEq z x) (synWbr (.cv z) A (.cv y))
      p0004
  have p0006 :=
    @gExbii (synWa (synWbr (.cv x) (synCid) (.cv z)) (synWbr (.cv z) A (.cv y)))
      (synWa (.objEq z x) (synWbr (.cv z) A (.cv y))) z p0005
  have p0007 := @gVex x
  have p0008 := @gBreq1 (.cv z) (.cv x) (.cv y) A
  have p0009 :=
    @gCeqsexv (synWbr (.cv z) A (.cv y)) (synWbr (.cv x) A (.cv y)) z (.cv x)
      dv_cache_0001 dv_cache_0005 p0007 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (synWb (synWex z (synWa (.objEq z x) (synWbr (.cv z) A (.cv y))))
        (synWbr (.cv x) A (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWbr synCop synCun synCnin synWnan synCcompl
          synWrex synCphi
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
    @gN3bitri (synWbr (.cv x) (synCcom A (synCid)) (.cv y))
      (synWex z (synWa (synWbr (.cv x) (synCid) (.cv z)) (synWbr (.cv z) A (.cv y))))
      (synWex z (synWa (.objEq z x) (synWbr (.cv z) A (.cv y))))
      (synWbr (.cv x) A (.cv y)) p0000 p0006 p0010_e02_recanon
  have p0011 :=
    @gEqbrriv x y (synCcom A (synCid)) A dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_coi2`. -/
@[expose]
noncomputable def gCoi2 (A : Class) : Nominal.NPrf (.classEq (synCcom (synCid) A) A) :=
  by
  have p0000 := @gCnvco (synCid) A
  have p0001 := @gCnvi
  have p0002 := @gCoeq2i (synCcnv (synCid)) (synCid) (synCcnv A) p0001
  have p0003 := @gCoi1 (synCcnv A)
  have p0004 :=
    @gN3eqtri (synCcnv (synCcom (synCid) A))
      (synCcom (synCcnv A) (synCcnv (synCid))) (synCcom (synCcnv A) (synCid))
      (synCcnv A) p0000 p0002 p0003
  have p0005 := @gCnveqb (synCcom (synCid) A) A
  have p0006 :=
    @gMpbir (.classEq (synCcom (synCid) A) A)
      (.classEq (synCcnv (synCcom (synCid) A)) (synCcnv A)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_coass`. -/
@[expose]
noncomputable def gCoass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCcom (synCcom A B) C) (synCcom A (synCcom B C))) :=
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
  have dv_cache_0005 : w ∉ ((synWbr (.cv x) C (.cv z))).fv :=
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
  have dv_cache_0010 : z ∉ ((synWbr (.cv w) A (.cv y))).fv :=
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
  have dv_cache_0012 : z ∉ ((synCcom A B)).fv :=
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
  have dv_cache_0014 : w ∉ ((synCcom B C)).fv :=
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
  have dv_cache_0015 : x ∉ ((synCcom (synCcom A B) C)).fv :=
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
  have dv_cache_0016 : y ∉ ((synCcom (synCcom A B) C)).fv :=
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
  have dv_cache_0017 : x ∉ ((synCcom A (synCcom B C))).fv :=
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
  have dv_cache_0018 : y ∉ ((synCcom A (synCcom B C))).fv :=
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
    @gExcom
      (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
        (synWbr (.cv w) A (.cv y)))
      w z
  have p0001 :=
    @gAnass (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w))
      (synWbr (.cv w) A (.cv y))
  have p0002 :=
    @gN2exbii
      (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
        (synWbr (.cv w) A (.cv y)))
      (synWa (synWbr (.cv x) C (.cv z))
        (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y))))
      z w p0001
  have p0003 :=
    @gBitr2i
      (synWex w (synWex z
          (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
            (synWbr (.cv w) A (.cv y)))))
      (synWex z (synWex w
          (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
            (synWbr (.cv w) A (.cv y)))))
      (synWex z (synWex w (synWa (synWbr (.cv x) C (.cv z))
            (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y))))))
      p0000 p0002
  have p0004 :=
    @gBrco w (.cv z) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @gAnbi2i (synWbr (.cv z) (synCcom A B) (.cv y))
      (synWex w (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y))))
      (synWbr (.cv x) C (.cv z)) p0004
  have p0006 :=
    @gN1942v (synWbr (.cv x) C (.cv z))
      (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y))) w dv_cache_0005
  have p0007 :=
    @gBitr4i
      (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) (synCcom A B) (.cv y)))
      (synWa (synWbr (.cv x) C (.cv z))
        (synWex w (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y)))))
      (synWex w (synWa (synWbr (.cv x) C (.cv z))
          (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y)))))
      p0005 p0006
  have p0008 :=
    @gExbii (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) (synCcom A B) (.cv y)))
      (synWex w (synWa (synWbr (.cv x) C (.cv z))
          (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y)))))
      z p0007
  have p0009 :=
    @gBrco z (.cv x) (.cv w) B C dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0010 :=
    @gAnbi1i (synWbr (.cv x) (synCcom B C) (.cv w))
      (synWex z (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w))))
      (synWbr (.cv w) A (.cv y)) p0009
  have p0011 :=
    @gN1941v (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
      (synWbr (.cv w) A (.cv y)) z dv_cache_0010
  have p0012 :=
    @gBitr4i
      (synWa (synWbr (.cv x) (synCcom B C) (.cv w)) (synWbr (.cv w) A (.cv y)))
      (synWa (synWex z (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w))))
        (synWbr (.cv w) A (.cv y)))
      (synWex z (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
          (synWbr (.cv w) A (.cv y))))
      p0010 p0011
  have p0013 :=
    @gExbii (synWa (synWbr (.cv x) (synCcom B C) (.cv w)) (synWbr (.cv w) A (.cv y)))
      (synWex z (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
          (synWbr (.cv w) A (.cv y))))
      w p0012
  have p0014 :=
    @gN3bitr4i
      (synWex z (synWex w (synWa (synWbr (.cv x) C (.cv z))
            (synWa (synWbr (.cv z) B (.cv w)) (synWbr (.cv w) A (.cv y))))))
      (synWex w (synWex z
          (synWa (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) B (.cv w)))
            (synWbr (.cv w) A (.cv y)))))
      (synWex z (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) (synCcom A B) (.cv y))))
      (synWex w (synWa (synWbr (.cv x) (synCcom B C) (.cv w)) (synWbr (.cv w) A (.cv y))))
      p0003 p0008 p0013
  have p0015 :=
    @gBrco z (.cv x) (.cv y) (synCcom A B) C dv_cache_0006 dv_cache_0011 dv_cache_0012
      dv_cache_0009
  have p0016 :=
    @gBrco w (.cv x) (.cv y) A (synCcom B C) dv_cache_0013 dv_cache_0002 dv_cache_0003
      dv_cache_0014
  have p0017 :=
    @gN3bitr4i
      (synWex z (synWa (synWbr (.cv x) C (.cv z)) (synWbr (.cv z) (synCcom A B) (.cv y))))
      (synWex w (synWa (synWbr (.cv x) (synCcom B C) (.cv w)) (synWbr (.cv w) A (.cv y))))
      (synWbr (.cv x) (synCcom (synCcom A B) C) (.cv y))
      (synWbr (.cv x) (synCcom A (synCcom B C)) (.cv y)) p0014 p0015 p0016
  have p0018 :=
    @gEqbrriv x y (synCcom (synCcom A B) C) (synCcom A (synCcom B C)) dv_cache_0015
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

/-- Checked nominal proof certificate identified upstream as `g_ssdmrn`. -/
@[expose]
noncomputable def gSsdmrn (A : Class) :
    Nominal.NPrf (synWss A (synCxp (synCdm A) (synCrn A))) :=
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
  have dv_cache_0003 : x ∉ ((synCxp (synCdm A) (synCrn A))).fv :=
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
  have dv_cache_0004 : y ∉ ((synCxp (synCdm A) (synCrn A))).fv :=
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
    @gSsrel x y A (synCxp (synCdm A) (synCrn A)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gOpeldm (.cv x) (.cv y) A
  have p0002 := @gOpelrn (.cv x) (.cv y) A
  have p0003 := @gOpelxp (.cv x) (.cv y) (synCdm A) (synCrn A)
  have p0004 :=
    @gSylanbrc (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (.cv x) (synCdm A))
      (.classMem (.cv y) (synCrn A))
      (.classMem (synCop (.cv x) (.cv y)) (synCxp (synCdm A) (synCrn A))) p0001 p0002
      p0003
  have p0005 := Nominal.gen p0004 y
  have p0006 :=
    @gMpgbir (synWss A (synCxp (synCdm A) (synCrn A)))
      (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) (synCxp (synCdm A) (synCrn A)))))
      x p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_dfcnv2`. -/
@[expose]
noncomputable def gDfcnv2 (A : Class) :
    Nominal.NPrf (.classEq (synCcnv A) (synCima (synCswap) A)) :=
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
  have dv_cache_0001 : z ∉ ((synCop (.cv y) (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classMem (synCop (.cv y) (.cv x)) A)).fv :=
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
  have dv_cache_0003 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0004 : z ∉ ((synCswap)).fv :=
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
  have dv_cache_0006 : x ∉ ((synCcnv A)).fv :=
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
  have dv_cache_0007 : y ∉ ((synCcnv A)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCima (synCswap) A)).fv :=
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
  have dv_cache_0009 : y ∉ ((synCima (synCswap) A)).fv :=
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
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 := @gBrswap2 (.cv z) (.cv x) (.cv y) p0000 p0001
  have p0003 :=
    @gAnbi1i (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))
      (.classEq (.cv z) (synCop (.cv y) (.cv x))) (.classMem (.cv z) A) p0002
  have p0004 :=
    @gExbii
      (synWa (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y))) (.classMem (.cv z) A))
      (synWa (.classEq (.cv z) (synCop (.cv y) (.cv x))) (.classMem (.cv z) A)) z p0003
  have p0005 := @gOpex (.cv y) (.cv x) p0001 p0000
  have p0006 := @gEleq1 (.cv z) (synCop (.cv y) (.cv x)) A
  have p0007 :=
    @gCeqsexv (.classMem (.cv z) A) (.classMem (synCop (.cv y) (.cv x)) A) z
      (synCop (.cv y) (.cv x)) dv_cache_0001 dv_cache_0002 p0005 p0006
  have p0008 :=
    @gBitri
      (synWex z (synWa (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      (synWex z (synWa (.classEq (.cv z) (synCop (.cv y) (.cv x))) (.classMem (.cv z) A)))
      (.classMem (synCop (.cv y) (.cv x)) A) p0004 p0007
  have p0009 :=
    @gElima z (synCop (.cv x) (.cv y)) (synCswap) A dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0010 :=
    (Nominal.biimpRefl (synWrex z A (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))))
  have p0011 :=
    @gExancom (.classMem (.cv z) A)
      (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y))) z
  have p0012 :=
    @gBitri (synWrex z A (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y))))
      (synWex z (synWa (.classMem (.cv z) A)
          (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))))
      (synWex z (synWa (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      p0010 p0011
  have p0013 :=
    @gBitri (.classMem (synCop (.cv x) (.cv y)) (synCima (synCswap) A))
      (synWrex z A (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y))))
      (synWex z (synWa (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      p0009 p0012
  have p0014 := @gOpelcnv (.cv x) (.cv y) A
  have p0015 :=
    @gN3bitr4ri
      (synWex z (synWa (synWbr (.cv z) (synCswap) (synCop (.cv x) (.cv y)))
          (.classMem (.cv z) A)))
      (.classMem (synCop (.cv y) (.cv x)) A)
      (.classMem (synCop (.cv x) (.cv y)) (synCima (synCswap) A))
      (.classMem (synCop (.cv x) (.cv y)) (synCcnv A)) p0008 p0013 p0014
  have p0016 :=
    @gEqrelriv x y (synCcnv A) (synCima (synCswap) A) dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_cnvexg`. -/
@[expose]
noncomputable def gCnvexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCcnv A) (synCvv))) :=
  by
  have p0000 := @gDfcnv2 A
  have p0001 := @gSwapex
  have p0002 := @gImaexg (synCswap) A (synCvv) V
  have p0003 :=
    @gMpan (.classMem (synCswap) (synCvv)) (.classMem A V)
      (.classMem (synCima (synCswap) A) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem A V) (synCcnv A) (synCima (synCswap) A) (synCvv) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cnvex`. -/
@[expose]
noncomputable def gCnvex (A : Class)
    (hyp_cnvex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCcnv A) (synCvv)) :=
  by
  have p0000 := @gCnvexg A (synCvv)
  have p0001 := Nominal.mp hyp_cnvex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rnexg`. -/
@[expose]
noncomputable def gRnexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCrn A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCrn A))
  have p0001 := @gVvex
  have p0002 := @gImaexg A (synCvv) V (synCvv)
  have p0003 :=
    @gMpan2 (.classMem A V) (.classMem (synCvv) (synCvv))
      (.classMem (synCima A (synCvv)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem A V) (synCrn A) (synCima A (synCvv)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dmexg`. -/
@[expose]
noncomputable def gDmexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCdm A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCdm A))
  have p0001 := @gCnvexg A V
  have p0002 := @gRnexg (synCcnv A) (synCvv)
  have p0003 :=
    @gSyl (.classMem A V) (.classMem (synCcnv A) (synCvv))
      (.classMem (synCrn (synCcnv A)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem A V) (synCdm A) (synCrn (synCcnv A)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dmex`. -/
@[expose]
noncomputable def gDmex (A : Class) (hyp_dmex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCdm A) (synCvv)) :=
  by
  have p0000 := @gDmexg A (synCvv)
  have p0001 := Nominal.mp hyp_dmex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rnex`. -/
@[expose]
noncomputable def gRnex (A : Class) (hyp_dmex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCrn A) (synCvv)) :=
  by
  have p0000 := @gRnexg A (synCvv)
  have p0001 := Nominal.mp hyp_dmex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_df2nd2`. -/
@[expose]
noncomputable def gDf2nd2 :
    Nominal.NPrf (.classEq (synC2nd) (synCcom (synC1st) (synCswap))) :=
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
  have dv_cache_0003 : z ∉ ((synWbr (.cv x) (synCswap) (.cv w))).fv :=
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
  have dv_cache_0004 : w ∉ ((synCop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0005 : w ∉ ((synWbr (.cv x) (synCswap) (synCop (.cv y) (.cv z)))).fv :=
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
  have dv_cache_0009 : x ∉ ((synC1st)).fv :=
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
  have dv_cache_0010 : y ∉ ((synC1st)).fv :=
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
  have dv_cache_0011 : w ∉ ((synC1st)).fv :=
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
  have dv_cache_0012 : x ∉ ((synCswap)).fv :=
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
  have dv_cache_0013 : y ∉ ((synCswap)).fv :=
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
  have dv_cache_0014 : w ∉ ((synCswap)).fv :=
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
  have p0000 := @gVex y
  have p0001 := @gBr1st z (.cv w) (.cv y) dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @gAnbi1i (synWbr (.cv w) (synC1st) (.cv y))
      (synWex z (.classEq (.cv w) (synCop (.cv y) (.cv z))))
      (synWbr (.cv x) (synCswap) (.cv w)) p0001
  have p0003 :=
    @gAncom (synWbr (.cv x) (synCswap) (.cv w)) (synWbr (.cv w) (synC1st) (.cv y))
  have p0004 :=
    @gN1941v (.classEq (.cv w) (synCop (.cv y) (.cv z)))
      (synWbr (.cv x) (synCswap) (.cv w)) z dv_cache_0003
  have p0005 :=
    @gN3bitr4i
      (synWa (synWbr (.cv w) (synC1st) (.cv y)) (synWbr (.cv x) (synCswap) (.cv w)))
      (synWa (synWex z (.classEq (.cv w) (synCop (.cv y) (.cv z))))
        (synWbr (.cv x) (synCswap) (.cv w)))
      (synWa (synWbr (.cv x) (synCswap) (.cv w)) (synWbr (.cv w) (synC1st) (.cv y)))
      (synWex z (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
          (synWbr (.cv x) (synCswap) (.cv w))))
      p0002 p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (synWbr (.cv x) (synCswap) (.cv w)) (synWbr (.cv w) (synC1st) (.cv y)))
      (synWex z (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
          (synWbr (.cv x) (synCswap) (.cv w))))
      w p0005
  have p0007 :=
    @gExcom
      (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
        (synWbr (.cv x) (synCswap) (.cv w)))
      z w
  have p0008 := @gVex z
  have p0009 := @gOpex (.cv y) (.cv z) p0000 p0008
  have p0010 := @gBreq2 (.cv w) (synCop (.cv y) (.cv z)) (.cv x) (synCswap)
  have p0011 :=
    @gCeqsexv (synWbr (.cv x) (synCswap) (.cv w))
      (synWbr (.cv x) (synCswap) (synCop (.cv y) (.cv z))) w (synCop (.cv y) (.cv z))
      dv_cache_0004 dv_cache_0005 p0009 p0010
  have p0012 := @gBrswap2 (.cv x) (.cv y) (.cv z) p0000 p0008
  have p0013 :=
    @gBitri
      (synWex w (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
          (synWbr (.cv x) (synCswap) (.cv w))))
      (synWbr (.cv x) (synCswap) (synCop (.cv y) (.cv z)))
      (.classEq (.cv x) (synCop (.cv z) (.cv y))) p0011 p0012
  have p0014 :=
    @gExbii
      (synWex w (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
          (synWbr (.cv x) (synCswap) (.cv w))))
      (.classEq (.cv x) (synCop (.cv z) (.cv y))) z p0013
  have p0015 :=
    @gN3bitr2ri
      (synWex w (synWa (synWbr (.cv x) (synCswap) (.cv w))
          (synWbr (.cv w) (synC1st) (.cv y))))
      (synWex w (synWex z (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
            (synWbr (.cv x) (synCswap) (.cv w)))))
      (synWex z (synWex w (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z)))
            (synWbr (.cv x) (synCswap) (.cv w)))))
      (synWex z (.classEq (.cv x) (synCop (.cv z) (.cv y)))) p0006 p0007 p0014
  have p0016 :=
    @gOpabbii (synWex z (.classEq (.cv x) (synCop (.cv z) (.cv y))))
      (synWex w (synWa (synWbr (.cv x) (synCswap) (.cv w))
          (synWbr (.cv w) (synC1st) (.cv y))))
      x y p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDf2nd x y z
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo x y w (synC1st)
      (synCswap) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0006 dv_cache_0015 dv_cache_0016
  have p0019 :=
    @gN3eqtr4i (synCopab x y (synWex z (.classEq (.cv x) (synCop (.cv z) (.cv y)))))
      (synCopab x y (synWex w (synWa (synWbr (.cv x) (synCswap) (.cv w))
            (synWbr (.cv w) (synC1st) (.cv y)))))
      (synC2nd) (synCcom (synC1st) (synCswap)) p0016 p0017 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_n_2ndex`. -/
@[expose]
noncomputable def gN2ndex : Nominal.NPrf (.classMem (synC2nd) (synCvv)) :=
  by
  have p0000 := @gDf2nd2
  have p0001 := @gN1stex
  have p0002 := @gSwapex
  have p0003 := @gCoex (synC1st) (synCswap) p0001 p0002
  have p0004 :=
    @gEqeltri (synC2nd) (synCcom (synC1st) (synCswap)) (synCvv) p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end
