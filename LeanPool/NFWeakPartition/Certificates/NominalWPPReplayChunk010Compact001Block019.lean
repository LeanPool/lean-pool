/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block018

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part060`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_elima (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B C)) (syn_wrex x C (syn_wbr (.cv x) B A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) A)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true])
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
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0007 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0008 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_wrex x C (syn_wbr (.cv x) B A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_C, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_B,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_elex A (syn_cima B C)
  have p0001 := @g_brex (.cv x) A B
  have p0002 :=
    @g_simprd (syn_wbr (.cv x) B A) (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv))
      p0001
  have p0003 :=
    @g_rexlimivw (syn_wbr (.cv x) B A) (.classMem A (syn_cvv)) x C dv_cache_0001 p0002
  have p0004 := @g_breq2 (.cv y) A (.cv x) B
  have p0005 :=
    @g_rexbidv (.classEq (.cv y) A) (syn_wbr (.cv x) B (.cv y)) (syn_wbr (.cv x) B A) x C
      dv_cache_0002 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x B C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_elab2g (syn_wrex x C (syn_wbr (.cv x) B (.cv y)))
      (syn_wrex x C (syn_wbr (.cv x) B A)) y A (syn_cima B C) (syn_cvv) dv_cache_0008
      dv_cache_0009 p0005 p0006
  have p0008 :=
    @g_pm5_21nii (.classMem A (syn_cima B C)) (.classMem A (syn_cvv))
      (syn_wrex x C (syn_wbr (.cv x) B A)) p0000 p0003 p0007
  exact p0008

@[expose]
noncomputable def g_elima2 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B C))
        (syn_wex x (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) B A)))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have p0000 := @g_elima x A B C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (syn_wrex x C (syn_wbr (.cv x) B A)))
  have p0002 :=
    @g_bitri (.classMem A (syn_cima B C)) (syn_wrex x C (syn_wbr (.cv x) B A))
      (syn_wex x (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) B A))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elima3 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B C))
        (syn_wex x (syn_wa (.classMem (.cv x) C) (.classMem (syn_cop (.cv x) A) B)))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have p0000 := @g_elima x A B C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) B A))
  have p0002 :=
    @g_rexbii (syn_wbr (.cv x) B A) (.classMem (syn_cop (.cv x) A) B) x C p0001
  have p0003 :=
    @g_bitri (.classMem A (syn_cima B C)) (syn_wrex x C (syn_wbr (.cv x) B A))
      (syn_wrex x C (.classMem (syn_cop (.cv x) A) B)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wrex x C (.classMem (syn_cop (.cv x) A) B)))
  have p0005 :=
    @g_bitri (.classMem A (syn_cima B C)) (syn_wrex x C (.classMem (syn_cop (.cv x) A) B))
      (syn_wex x (syn_wa (.classMem (.cv x) C) (.classMem (syn_cop (.cv x) A) B))) p0003
      p0004
  exact p0005

@[expose]
noncomputable def g_brssetg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (syn_wbr A (syn_csset) B) (syn_wss A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
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
  have dv_cache_0006 : x ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_sseq1 (.cv x) A (.cv y)
  have p0001 := @g_sseq2 (.cv y) B A
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sset x y
      dv_cache_0001
  have p0003 :=
    @g_brabg (syn_wss (.cv x) (.cv y)) (syn_wss A (.cv y)) (syn_wss A B) x y A B V W
      (syn_csset) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_brsset (A : Class) (B : Class)
    (hyp_brsset_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brsset_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_csset) B) (syn_wss A B)) :=
  by
  have p0000 := @g_brssetg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr A (syn_csset) B) (syn_wss A B)) hyp_brsset_1 hyp_brsset_2 p0000
  exact p0001

@[expose]
noncomputable def g_brssetsn (A : Class) (B : Class)
    (hyp_brssetsn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brssetsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn A) (syn_csset) B) (.classMem A B)) :=
  by
  have p0000 := @g_snex A
  have p0001 := @g_brsset (syn_csn A) B p0000 hyp_brssetsn_2
  have p0002 := @g_snss A B hyp_brssetsn_1
  have p0003 :=
    @g_bitr4i (syn_wbr (syn_csn A) (syn_csset) B) (syn_wss (syn_csn A) B) (.classMem A B)
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_opelssetsn (A : Class) (B : Class)
    (hyp_brssetsn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brssetsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn A) B) (syn_csset)) (.classMem A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr (syn_csn A) (syn_csset) B))
  have p0001 := @g_brssetsn A B hyp_brssetsn_1 hyp_brssetsn_2
  have p0002 :=
    @g_bitr3i (.classMem (syn_cop (syn_csn A) B) (syn_csset))
      (syn_wbr (syn_csn A) (syn_csset) B) (.classMem A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_brsi (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_csi R) B) (syn_wex x (syn_wex y
            (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
              (syn_wbr (.cv x) R (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 :
    x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          dv_B_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_y,
          dv_B_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv w) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv w) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0009 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0010 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0011 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0012 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0013 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0014 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0015 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0016 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0017 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0018 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0019 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0020 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0021 :
    z ∉
      ((syn_wex x (syn_wex y
            (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
              (syn_wbr (.cv x) R (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y,
          fresh_z_not_R, fresh_z_not_A, fresh_z_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0022 :
    w ∉
      ((syn_wex x (syn_wex y
            (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
              (syn_wbr (.cv x) R (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y,
          fresh_w_not_R, fresh_w_not_A, fresh_w_not_B, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_brex A B (syn_csi R)
  have p0001 := @g_snex (.cv x)
  have p0002 := @g_snex (.cv y)
  have p0003 :=
    @g_pm3_2i (.classMem (syn_csn (.cv x)) (syn_cvv))
      (.classMem (syn_csn (.cv y)) (syn_cvv)) p0001 p0002
  have p0004 := @g_eleq1 A (syn_csn (.cv x)) (syn_cvv)
  have p0005 := @g_eleq1 B (syn_csn (.cv y)) (syn_cvv)
  have p0006 :=
    @g_bi2anan9 (.classEq A (syn_csn (.cv x))) (.classMem A (syn_cvv))
      (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classEq B (syn_csn (.cv y)))
      (.classMem B (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_mpbiri (syn_wa (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem (syn_csn (.cv y)) (syn_cvv)))
      p0003 p0006
  have p0008 :=
    @g_n_3adant3 (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr (.cv x) R (.cv y))
      p0007
  have p0009 :=
    @g_exlimivv
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) x y dv_cache_0001
      dv_cache_0002 p0008
  have p0010 := @g_eqeq1 (.cv z) A (syn_csn (.cv x))
  have p0011 :=
    @g_n_3anbi1d (.classEq (.cv z) A) (.classEq (.cv z) (syn_csn (.cv x)))
      (.classEq A (syn_csn (.cv x))) (.classEq (.cv w) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0010
  have p0012 :=
    @g_n_2exbidv (.classEq (.cv z) A)
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv x))) (.classEq (.cv w) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv w) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      x y dv_cache_0003 dv_cache_0004 p0011
  have p0013 := @g_eqeq1 (.cv w) B (syn_csn (.cv y))
  have p0014 :=
    @g_n_3anbi2d (.classEq (.cv w) B) (.classEq (.cv w) (syn_csn (.cv y)))
      (.classEq B (syn_csn (.cv y))) (.classEq A (syn_csn (.cv x)))
      (syn_wbr (.cv x) R (.cv y)) p0013
  have p0015 :=
    @g_n_2exbidv (.classEq (.cv w) B)
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv w) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      x y dv_cache_0005 dv_cache_0006 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_si z w x y R
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0017 :=
    @g_brabg
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv x)))
            (.classEq (.cv w) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv w) (syn_csn (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      z w A B (syn_cvv) (syn_cvv) (syn_csi R) dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0014 p0012 p0015 p0016
  have p0018 :=
    @g_pm5_21nii (syn_wbr A (syn_csi R) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      p0000 p0009 p0017
  exact p0018

@[expose]
noncomputable def g_xpeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cxp A C) (syn_cxp B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have p0000 := @g_eleq2 A B (.cv x)
  have p0001 :=
    @g_anbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv y) C) p0000
  have p0002 :=
    @g_opabbidv (.classEq A B) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y dv_cache_0001 dv_cache_0002
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B C
      dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) (syn_cxp A C)
      (syn_cxp B C) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_xpeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cxp C A) (syn_cxp C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have p0000 := @g_eleq2 A B (.cv y)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classMem (.cv y) A) (.classMem (.cv y) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_opabbidv (.classEq A B) (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) A))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) B)) x y dv_cache_0001 dv_cache_0002
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y C A
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y C B
      dv_cache_0003 dv_cache_0004 dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) A)))
      (syn_copab x y (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) B))) (syn_cxp C A)
      (syn_cxp C B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_elxp (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cxp B C)) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
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
        simp only [dv_A_y, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B C
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cxp B C)
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) A p0000
  have p0002 :=
    @g_elopab (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y A dv_cache_0006
      dv_cache_0007
  have p0003 :=
    @g_bitri (.classMem A (syn_cxp B C))
      (.classMem A (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_elxp2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cxp B C))
        (syn_wrex x B (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y)))))) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classMem (.cv x) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_B_y, or_false, not_false_eq_true])
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
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
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    (Nominal.biimpRefl (syn_wrex y C
        (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cop (.cv x) (.cv y))))))
  have p0001 :=
    @g_r19_42v (.classMem (.cv x) B) (.classEq A (syn_cop (.cv x) (.cv y))) y C
      dv_cache_0001
  have p0002 :=
    @g_an13 (.classMem (.cv y) C) (.classMem (.cv x) B)
      (.classEq A (syn_cop (.cv x) (.cv y)))
  have p0003 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) C)
        (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cop (.cv x) (.cv y)))))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      y p0002
  have p0004 :=
    @g_n_3bitr3i
      (syn_wrex y C (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cop (.cv x) (.cv y)))))
      (syn_wex y (syn_wa (.classMem (.cv y) C)
          (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cop (.cv x) (.cv y))))))
      (syn_wa (.classMem (.cv x) B) (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y)))))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      p0000 p0001 p0003
  have p0005 :=
    @g_exbii
      (syn_wa (.classMem (.cv x) B) (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y)))))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      x p0004
  have p0006 :=
    (Nominal.biimpRefl (syn_wrex x B (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y))))))
  have p0007 :=
    @g_elxp x y A B C dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_n_3bitr4ri
      (syn_wex x (syn_wa (.classMem (.cv x) B)
          (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      (syn_wrex x B (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y)))))
      (.classMem A (syn_cxp B C)) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_xpeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_cxp A C) (syn_cxp B D))) :=
  by
  have p0000 := @g_xpeq1 A B C
  have p0001 := @g_xpeq2 C D B
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_cxp A C) (syn_cxp B C) (syn_cxp B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_xpeq1i (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cxp A C) (syn_cxp B C)) :=
  by
  have p0000 := @g_xpeq1 A B C
  have p0001 := Nominal.mp hyp_xpeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_xpeq2i (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cxp C A) (syn_cxp C B)) :=
  by
  have p0000 := @g_xpeq2 A B C
  have p0001 := Nominal.mp hyp_xpeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_xpeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_xpeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cxp A C) (syn_cxp B D)) :=
  by
  have p0000 := @g_xpeq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cxp A C) (syn_cxp B D))
      hyp_xpeq12i_1 hyp_xpeq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_xpeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cxp A C) (syn_cxp B C))) :=
  by
  have p0000 := @g_xpeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cxp A C) (syn_cxp B C)) hyp_xpeq1d_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part061`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_xpeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cxp C A) (syn_cxp C B))) :=
  by
  have p0000 := @g_xpeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cxp C A) (syn_cxp C B)) hyp_xpeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_xpeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_xpeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cxp A C) (syn_cxp B D))) :=
  by
  have p0000 := @g_xpeq12 A B C D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cxp A C) (syn_cxp B D))
      hyp_xpeq1d_1 hyp_xpeq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_nfxp (x : Var) (A : Class) (B : Class)
    (hyp_nfxp_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfxp_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnfc x (syn_cxp A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0009 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp y z A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @g_nfcri x y A dv_cache_0006 hyp_nfxp_1
  have p0002 := @g_nfcri x z B dv_cache_0007 hyp_nfxp_2
  have p0003 := @g_nfan (.classMem (.cv y) A) (.classMem (.cv z) B) x p0001 p0002
  have p0004 :=
    @g_nfopab (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) y z x dv_cache_0008
      dv_cache_0009 p0003
  have p0005 :=
    @g_nfcxfr x (syn_cxp A B)
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_opelxp (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A B) (syn_cxp C D))
        (syn_wa (.classMem A C) (.classMem B D))) :=
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
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cop A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0006 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0010 : y ∉ ((syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_B, fresh_x_not_D, or_false,
          not_false_eq_true])
  have p0000 := @g_eqcom (syn_cop A B) (syn_cop (.cv x) (.cv y))
  have p0001 := @g_opth (.cv x) (.cv y) A B
  have p0002 :=
    @g_bitri (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0001
  have p0003 :=
    @g_anbi1i (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0002
  have p0004 :=
    @g_an4 (.classEq (.cv x) A) (.classEq (.cv y) B) (.classMem (.cv x) C)
      (.classMem (.cv y) D)
  have p0005 :=
    @g_bitri
      (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (syn_wa (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (syn_wa (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))
        (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D)))
      p0003 p0004
  have p0006 :=
    @g_n_2exbii
      (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (syn_wa (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))
        (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D)))
      x y p0005
  have p0007 :=
    @g_elxp x y (syn_cop A B) C D dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A C
      dv_cache_0008 dv_cache_0003)
  have p0009 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y B D
      dv_cache_0009 dv_cache_0006)
  have p0010 :=
    @g_anbi12i (.classMem A C)
      (syn_wex x (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))) (.classMem B D)
      (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D))) p0008 p0009
  have p0011 :=
    @g_eeanv (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))
      (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D)) x y dv_cache_0010 dv_cache_0011
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem A C) (.classMem B D))
      (syn_wa (syn_wex x (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C)))
        (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))
            (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D)))))
      p0010 p0011
  have p0013 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))
            (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) D)))))
      (.classMem (syn_cop A B) (syn_cxp C D)) (syn_wa (.classMem A C) (.classMem B D))
      p0006 p0007 p0012
  exact p0013

@[expose]
noncomputable def g_brxp (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cxp C D) B) (syn_wa (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr A (syn_cxp C D) B))
  have p0001 := @g_opelxp A B C D
  have p0002 :=
    @g_bitri (syn_wbr A (syn_cxp C D) B) (.classMem (syn_cop A B) (syn_cxp C D))
      (syn_wa (.classMem A C) (.classMem B D)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fconstopab (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cxp A (syn_csn B))
        (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) :=
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
  have dv_cache_0003 : x ∉ ((syn_csn B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_B_x,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_csn B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_B_y,
          not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A (syn_csn B)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y B dv_cache_0006
  have p0002 := @g_eqabri (.classEq (.cv y) B) y (syn_csn B) p0001
  have p0003 :=
    @g_anbi2i (.classMem (.cv y) (syn_csn B)) (.classEq (.cv y) B) (.classMem (.cv x) A)
      p0002
  have p0004 :=
    @g_opabbii (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_csn B)))
      (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y p0003
  have p0005 :=
    @g_eqtri (syn_cxp A (syn_csn B))
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_csn B))))
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_xpiundir (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (.classEq (syn_cxp (syn_ciun x A B) C) (syn_ciun x A (syn_cxp B C))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0004 :
    x ∉ ((syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_x, fresh_x_ne_z, fresh_x_ne_y,
          fresh_x_ne_w, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0008 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
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
  have dv_cache_0010 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0011 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0012 : y ∉ ((syn_ciun x A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          Finset.mem_union, Finset.mem_erase, fresh_y_not_A, fresh_y_not_B, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_ciun x A B)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          Finset.mem_union, Finset.mem_erase, fresh_w_not_A, fresh_w_not_B, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_cxp (syn_ciun x A B) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, Finset.mem_union,
          Finset.mem_erase, fresh_z_not_A, fresh_z_not_B, fresh_z_not_C, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_ciun x A (syn_cxp B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_erase, fresh_z_not_A, fresh_z_not_B, fresh_z_not_C, or_false,
          and_false, not_false_eq_true])
  have p0000 :=
    @g_rexcom4
      (syn_wa (.classMem (.cv y) B) (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      x y A dv_cache_0001 dv_cache_0002
  have p0001 :=
    (Nominal.biimpRefl
      (syn_wrex y B (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
  have p0002 :=
    @g_rexbii (syn_wrex y B (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      (syn_wex y (syn_wa (.classMem (.cv y) B)
          (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      x A p0001
  have p0003 := @g_eliun x (.cv y) A B dv_cache_0003
  have p0004 :=
    @g_anbi1i (.classMem (.cv y) (syn_ciun x A B)) (syn_wrex x A (.classMem (.cv y) B))
      (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))) p0003
  have p0005 :=
    @g_r19_41v (.classMem (.cv y) B)
      (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))) x A dv_cache_0004
  have p0006 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_ciun x A B))
        (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      (syn_wa (syn_wrex x A (.classMem (.cv y) B))
        (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      (syn_wrex x A (syn_wa (.classMem (.cv y) B)
          (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      p0004 p0005
  have p0007 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_ciun x A B))
        (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      (syn_wrex x A (syn_wa (.classMem (.cv y) B)
          (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      y p0006
  have p0008 :=
    @g_n_3bitr4ri
      (syn_wrex x A (syn_wex y (syn_wa (.classMem (.cv y) B)
            (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))))
      (syn_wex y (syn_wrex x A (syn_wa (.classMem (.cv y) B)
            (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))))
      (syn_wrex x A (syn_wrex y B (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_ciun x A B))
          (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      p0000 p0002 p0007
  have p0009 :=
    (Nominal.biimpRefl (syn_wrex y (syn_ciun x A B)
        (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
  have p0010 :=
    @g_elxp2 y w (.cv z) B C dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0011 :=
    @g_rexbii (.classMem (.cv z) (syn_cxp B C))
      (syn_wrex y B (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))) x A p0010
  have p0012 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_ciun x A B))
          (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      (syn_wrex x A (syn_wrex y B (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w))))))
      (syn_wrex y (syn_ciun x A B) (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      (syn_wrex x A (.classMem (.cv z) (syn_cxp B C))) p0008 p0009 p0011
  have p0013 :=
    @g_elxp2 y w (.cv z) (syn_ciun x A B) C dv_cache_0005 dv_cache_0006 dv_cache_0012
      dv_cache_0013 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0014 := @g_eliun x (.cv z) A (syn_cxp B C) dv_cache_0014
  have p0015 :=
    @g_n_3bitr4i
      (syn_wrex y (syn_ciun x A B) (syn_wrex w C (.classEq (.cv z) (syn_cop (.cv y) (.cv w)))))
      (syn_wrex x A (.classMem (.cv z) (syn_cxp B C)))
      (.classMem (.cv z) (syn_cxp (syn_ciun x A B) C))
      (.classMem (.cv z) (syn_ciun x A (syn_cxp B C))) p0012 p0013 p0014
  have p0016 :=
    @g_eqriv z (syn_cxp (syn_ciun x A B) C) (syn_ciun x A (syn_cxp B C)) dv_cache_0015
      dv_cache_0016 p0015
  exact p0016

@[expose]
noncomputable def g_iunxpconst (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.classEq (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) (syn_cxp A B)) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
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
  have p0000 := @g_xpiundir x A (syn_csn (.cv x)) B dv_cache_0001
  have p0001 := @g_iunid x A dv_cache_0002
  have p0002 := @g_xpeq1i (syn_ciun x A (syn_csn (.cv x))) A B p0001
  have p0003 :=
    @g_eqtr3i (syn_cxp (syn_ciun x A (syn_csn (.cv x))) B)
      (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) (syn_cxp A B) p0000 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part062`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_opeliunxp (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
        (syn_wa (.classMem (.cv x) A) (.classMem C B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 :
    z ∉
      ((syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_B,
          or_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : x ∉ ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_z,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv y) (syn_cop (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_C, or_false,
          not_false_eq_true])
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
  have dv_cache_0008 : y ∉ ((syn_cxp (syn_csn (.cv x)) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cop (.cv x) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C)
              (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A,
          fresh_y_ne_z, fresh_y_not_C, fresh_y_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv x)).fv :=
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
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wa (.classMem (.cv x) A) (.classMem C B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_not_C, fresh_z_not_B,
          or_false, not_false_eq_true])
  have p0000 := @g_elex (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
  have p0001 := @g_opexb (.cv x) C
  have p0002 :=
    @g_simprbi (.classMem (syn_cop (.cv x) C) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (.classMem C (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (.classMem (syn_cop (.cv x) C) (syn_cvv)) (.classMem C (syn_cvv)) p0000 p0002
  have p0004 := @g_elex C B
  have p0005 :=
    @g_adantl (.classMem C B) (.classMem C (syn_cvv)) (.classMem (.cv x) A) p0004
  have p0006 := @g_vex x
  have p0007 := @g_opexg (.cv x) C (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_mpan (.classMem (.cv x) (syn_cvv)) (.classMem C (syn_cvv))
      (.classMem (syn_cop (.cv x) C) (syn_cvv)) p0006 p0007
  have p0009 :=
    (Nominal.biimpRefl (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))))
  have p0010 :=
    @g_nfv
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))) z
      dv_cache_0001
  have p0011 := @g_nfs1v (.classMem (.cv x) A) x z dv_cache_0002
  have p0012 := @g_nfcv x (syn_csn (.cv z)) dv_cache_0003
  have p0013 := @g_nfcsb1v x (.cv z) B dv_cache_0004
  have p0014 := @g_nfxp x (syn_csn (.cv z)) (syn_csb (.cv z) x B) p0012 p0013
  have p0015 :=
    @g_nfcri x y (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)) dv_cache_0005 p0014
  have p0016 :=
    @g_nfan (syn_wsb z x (.classMem (.cv x) A))
      (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) x p0011 p0015
  have p0017 := @g_sbequ12 (.classMem (.cv x) A) x z
  have p0018 := @g_sneq (.cv x) (.cv z)
  have p0019 := @g_csbeq1a x (.cv z) B
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0020_e01_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq B (syn_csb (.cv z) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csb syn_wsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @g_xpeq12d (.objEq x z) (syn_csn (.cv x)) (syn_csn (.cv z)) B (syn_csb (.cv z) x B)
      p0020_e00_recanon p0020_e01_recanon
  have p0021 :=
    @g_eleq2d (.objEq x z) (syn_cxp (syn_csn (.cv x)) B)
      (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)) (.cv y) p0020
  have p0022 :=
    @g_anbi12d (.objEq x z) (.classMem (.cv x) A) (syn_wsb z x (.classMem (.cv x) A))
      (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))
      (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) p0017 p0021
  have p0023 :=
    @g_cbvex
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wa (syn_wsb z x (.classMem (.cv x) A))
        (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))
      x z p0010 p0016 p0022
  have p0024 :=
    @g_bitri (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wex x
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))))
      (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A))
          (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))
      p0009 p0023
  have p0025 :=
    @g_eleq1 (.cv y) (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))
  have p0026 :=
    @g_anbi2d (.classEq (.cv y) (syn_cop (.cv x) C))
      (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))
      (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))
      (syn_wsb z x (.classMem (.cv x) A)) p0025
  have p0027 :=
    @g_exbidv (.classEq (.cv y) (syn_cop (.cv x) C))
      (syn_wa (syn_wsb z x (.classMem (.cv x) A))
        (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))
      (syn_wa (syn_wsb z x (.classMem (.cv x) A))
        (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))
      z dv_cache_0006 p0026
  have p0028 :=
    @g_syl5bb (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A))
          (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))
      (.classEq (.cv y) (syn_cop (.cv x) C))
      (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C)
            (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))
      p0024 p0027
  have p0029 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y A
      (syn_cxp (syn_csn (.cv x)) B) dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0030 :=
    @g_elab2g (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C)
            (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))
      y (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) (syn_cvv)
      dv_cache_0009 dv_cache_0010 p0028 p0029
  have p0031 :=
    @g_syl (.classMem C (syn_cvv)) (.classMem (syn_cop (.cv x) C) (syn_cvv))
      (syn_wb (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
        (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C)
              (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))))
      p0008 p0030
  have p0032 := @g_opelxp (.cv x) C (syn_csn (.cv z)) (syn_csb (.cv z) x B)
  have p0033 :=
    @g_anbi2i
      (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))
      (syn_wa (.classMem (.cv x) (syn_csn (.cv z))) (.classMem C (syn_csb (.cv z) x B)))
      (syn_wsb z x (.classMem (.cv x) A)) p0032
  have p0034 :=
    @g_an12 (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv x) (syn_csn (.cv z)))
      (.classMem C (syn_csb (.cv z) x B))
  have p0035 := @g_elsn x (.cv z) dv_cache_0004
  have p0036 := @g_equcom x z
  have p0037_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_csn (.cv z))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0037 :=
    @g_bitri (.classMem (.cv x) (syn_csn (.cv z))) (.objEq x z) (.objEq z x)
      p0037_e00_recanon p0036
  have p0038 :=
    @g_anbi1i (.classMem (.cv x) (syn_csn (.cv z))) (.objEq z x)
      (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B)))
      p0037
  have p0039 :=
    @g_n_3bitri
      (syn_wa (syn_wsb z x (.classMem (.cv x) A))
        (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))
      (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) (syn_csn (.cv z)))
          (.classMem C (syn_csb (.cv z) x B))))
      (syn_wa (.classMem (.cv x) (syn_csn (.cv z)))
        (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))))
      (syn_wa (.objEq z x)
        (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))))
      p0033 p0034 p0038
  have p0040 :=
    @g_exbii
      (syn_wa (syn_wsb z x (.classMem (.cv x) A))
        (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))
      (syn_wa (.objEq z x)
        (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))))
      z p0039
  have p0041 := @g_sbequ12r (.classMem (.cv x) A) z x
  have p0042_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq B (syn_csb (.cv z) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csb syn_wsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0042 := @g_equcoms (.classEq B (syn_csb (.cv z) x B)) x z p0042_e00_recanon
  have p0043 := @g_eqcomd (.objEq z x) B (syn_csb (.cv z) x B) p0042
  have p0044 := @g_eleq2d (.objEq z x) (syn_csb (.cv z) x B) B C p0043
  have p0045 :=
    @g_anbi12d (.objEq z x) (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv x) A)
      (.classMem C (syn_csb (.cv z) x B)) (.classMem C B) p0041 p0044
  have p0046_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (syn_wb
          (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B)))
          (syn_wa (.classMem (.cv x) A) (.classMem C B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wsb syn_csb syn_wsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @g_ceqsexv
      (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B)))
      (syn_wa (.classMem (.cv x) A) (.classMem C B)) z (.cv x) dv_cache_0011 dv_cache_0012
      p0006 p0046_e01_recanon
  have p0047_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex z (syn_wa (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A))
              (.classMem C (syn_csb (.cv z) x B)))))
        (syn_wa (.classMem (.cv x) A) (.classMem C B))) :=
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
      p0046
  have p0047 :=
    @g_bitri
      (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C)
            (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))
      (syn_wex z (syn_wa (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A))
            (.classMem C (syn_csb (.cv z) x B)))))
      (syn_wa (.classMem (.cv x) A) (.classMem C B)) p0040 p0047_e01_recanon
  have p0048 :=
    @g_syl6bb (.classMem C (syn_cvv))
      (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C)
            (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))
      (syn_wa (.classMem (.cv x) A) (.classMem C B)) p0031 p0047
  have p0049 :=
    @g_pm5_21nii
      (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (.classMem C (syn_cvv)) (syn_wa (.classMem (.cv x) A) (.classMem C B)) p0003 p0005
      p0048
  exact p0049

@[expose]
noncomputable def g_eliunxp (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wex x (syn_wex y
            (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
              (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))) :=
  by
  have dv_cache_0001 : x ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0004 :
    y ∉ ((Wff.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_C_y, dv_A_y, (Ne.symm dv_x_y), dv_B_y, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_elex C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
  have p0001 :=
    @g_pm4_71ri (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (.classMem C (syn_cvv)) p0000
  have p0002 := @g_opeqexb x y C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_anbi1i (.classMem C (syn_cvv))
      (syn_wex x (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))))
      (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) p0002
  have p0004 :=
    @g_bitri (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wa (.classMem C (syn_cvv))
        (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))
      (syn_wa (syn_wex x (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))))
        (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))
      p0001 p0003
  have p0005 := @g_nfiu1 x A (syn_cxp (syn_csn (.cv x)) B)
  have p0006 :=
    @g_nfel2 x C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) dv_cache_0001 p0005
  have p0007 :=
    @g_n_19_41 (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))
      (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) x p0006
  have p0008 :=
    @g_n_19_41v (.classEq C (syn_cop (.cv x) (.cv y)))
      (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) y dv_cache_0004
  have p0009 :=
    @g_eleq1 C (syn_cop (.cv x) (.cv y)) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
  have p0010 := @g_opeliunxp x A B (.cv y)
  have p0011 :=
    @g_syl6bb (.classEq C (syn_cop (.cv x) (.cv y)))
      (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0009 p0010
  have p0012 :=
    @g_pm5_32i (.classEq C (syn_cop (.cv x) (.cv y)))
      (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0011
  have p0013 :=
    @g_exbii
      (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
        (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))
      (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      y p0012
  have p0014 :=
    @g_bitr3i
      (syn_wa (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))
        (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))
      (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
          (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))))
      (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))
      p0008 p0013
  have p0015 :=
    @g_exbii
      (syn_wa (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))
        (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))
      (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))
      x p0014
  have p0016 :=
    @g_n_3bitr2i (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wa (syn_wex x (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))))
        (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))
      (syn_wex x (syn_wa (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))
          (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))))
      (syn_wex x (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      p0004 p0007 p0015
  exact p0016

@[expose]
noncomputable def g_raliunxp (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (_dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_raliunxp_1 :
      Nominal.NPrf (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph)
        (syn_wral y A (syn_wral z B ps))) :=
  by
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0002 : z ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_z), not_false_eq_true])
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0006 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0007 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_x_z, or_false, not_false_eq_true])
  have dv_cache_0009 :
    x ∉ ((Wff.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_A_x, dv_x_z, dv_B_x, dv_ps_x, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_eliunxp y z A B (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
            (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)))))
      ph p0000
  have p0002 :=
    @g_n_19_23vv
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
        (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)))
      ph y z dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_bitr4i (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph)
      (.imp (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
              (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))))) ph)
      (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
              (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))
      p0001 p0002
  have p0004 :=
    @g_albii (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph)
      (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
              (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))
      x p0003
  have p0005 :=
    @g_alrot3
      (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
          (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)
      x y z
  have p0006 :=
    @g_impexp (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph
  have p0007 :=
    @g_albii
      (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
          (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)
      (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
        (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph))
      x p0006
  have p0008 := @g_vex y
  have p0009 := @g_vex z
  have p0010 := @g_opex (.cv y) (.cv z) p0008 p0009
  have p0011 :=
    @g_imbi2d (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) ph ps
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) hyp_raliunxp_1
  have p0012 :=
    @g_ceqsalv (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph)
      (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) x
      (syn_cop (.cv y) (.cv z)) dv_cache_0008 dv_cache_0009 p0010 p0011
  have p0013 :=
    @g_bitri
      (.all x (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
            (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))
      (.all x (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
          (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph)))
      (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) p0007 p0012
  have p0014 :=
    @g_n_2albii
      (.all x (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
            (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))
      (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) y z p0013
  have p0015 :=
    @g_bitri
      (.all x (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
                (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))))
      (.all y (.all z (.all x (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
                (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))))
      (.all y (.all z (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)))
      p0005 p0014
  have p0016 :=
    @g_bitri
      (.all x (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph))
      (.all x (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
                (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))))
      (.all y (.all z (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)))
      p0004 p0015
  have p0017 :=
    (Nominal.biimpRefl (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph))
  have p0018 := @g_r2al ps y z A B dv_cache_0001 dv_cache_0005
  have p0019 :=
    @g_n_3bitr4i
      (.all x (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph))
      (.all y (.all z (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)))
      (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph)
      (syn_wral y A (syn_wral z B ps)) p0016 p0017 p0018
  exact p0019

@[expose]
noncomputable def g_rexiunxp (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_raliunxp_1 :
      Nominal.NPrf (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wrex x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph)
        (syn_wrex y A (syn_wrex z B ps))) :=
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
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.neg ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, dv_ph_y, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.neg ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, dv_ph_z, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.neg ps)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, dv_ps_x, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0010 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0011 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_notbid (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) ph ps hyp_raliunxp_1
  have p0001 :=
    @g_raliunxp (.neg ph) (.neg ps) x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0000
  have p0002 := @g_ralnex ps z B
  have p0003 := @g_ralbii (syn_wral z B (.neg ps)) (.neg (syn_wrex z B ps)) y A p0002
  have p0004 :=
    @g_bitri (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (.neg ph))
      (syn_wral y A (syn_wral z B (.neg ps))) (syn_wral y A (.neg (syn_wrex z B ps)))
      p0001 p0003
  have p0005 :=
    @g_notbii (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (.neg ph))
      (syn_wral y A (.neg (syn_wrex z B ps))) p0004
  have p0006 := @g_dfrex2 ph x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))
  have p0007 := @g_dfrex2 (syn_wrex z B ps) y A
  have p0008 :=
    @g_n_3bitr4i
      (.neg (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (.neg ph)))
      (.neg (syn_wral y A (.neg (syn_wrex z B ps))))
      (syn_wrex x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph)
      (syn_wrex y A (syn_wrex z B ps)) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_rexxp (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_raliunxp_1 :
      Nominal.NPrf (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wrex x (syn_cxp A B) ph) (syn_wrex y A (syn_wrex z B ps))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_B_x, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
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
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0009 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0010 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0011 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0013 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0014 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @g_iunxpconst y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_rexeqi ph x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (syn_cxp A B)
      dv_cache_0003 dv_cache_0004 p0000
  have p0002 :=
    @g_rexiunxp ph ps x y z A B dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 hyp_raliunxp_1
  have p0003 :=
    @g_bitr3i (syn_wrex x (syn_cxp A B) ph)
      (syn_wrex x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph)
      (syn_wrex y A (syn_wrex z B ps)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_brel (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_brelg_1 : Nominal.NPrf (syn_wss R (syn_cxp C D))) :
    Nominal.NPrf (.imp (syn_wbr A R B) (syn_wa (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := @g_ssbri R (syn_cxp C D) A B hyp_brelg_1
  have p0001 := @g_brxp A B C D
  have p0002 :=
    @g_sylib (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B)
      (syn_wa (.classMem A C) (.classMem B D)) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part063`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_xpundi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cxp A (syn_cun B C)) (syn_cun (syn_cxp A B) (syn_cxp A C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have dv_cache_0003 : x ∉ ((syn_cun B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cun B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0008 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
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
  have p0000 := @g_elun (.cv y) B C
  have p0001 :=
    @g_anbi2i (.classMem (.cv y) (syn_cun B C))
      (syn_wo (.classMem (.cv y) B) (.classMem (.cv y) C)) (.classMem (.cv x) A) p0000
  have p0002 := @g_andi (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv y) C)
  have p0003 :=
    @g_bitri (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C)))
      (syn_wa (.classMem (.cv x) A) (syn_wo (.classMem (.cv y) B) (.classMem (.cv y) C)))
      (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      p0001 p0002
  have p0004 :=
    @g_opabbii (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C)))
      (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      x y p0003
  have p0005 :=
    @g_unopab (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)) x y
  have p0006 :=
    @g_eqtr4i
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C))))
      (syn_copab x y (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))))
      (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))))
      p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A
      (syn_cun B C) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0005
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A C
      dv_cache_0001 dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0005
  have p0010 :=
    @g_uneq12i (syn_cxp A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_cxp A C)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) p0008 p0009
  have p0011 :=
    @g_n_3eqtr4i
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C))))
      (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))))
      (syn_cxp A (syn_cun B C)) (syn_cun (syn_cxp A B) (syn_cxp A C)) p0006 p0007 p0010
  exact p0011

@[expose]
noncomputable def g_xpundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (syn_cxp (syn_cun A B) C) (syn_cun (syn_cxp A C) (syn_cxp B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cun A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have p0000 := @g_elun (.cv x) A B
  have p0001 :=
    @g_anbi1i (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv y) C) p0000
  have p0002 := @g_andir (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv y) C)
  have p0003 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C))
      (syn_wa (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv y) C))
      (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      p0001 p0002
  have p0004 :=
    @g_opabbii (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C))
      (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      x y p0003
  have p0005 :=
    @g_unopab (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y
  have p0006 :=
    @g_eqtr4i
      (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C)))
      (syn_copab x y (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))
          (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))
        (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y (syn_cun A B)
      C dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A C
      dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B C
      dv_cache_0008 dv_cache_0009 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0010 :=
    @g_uneq12i (syn_cxp A C)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) (syn_cxp B C)
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) p0008 p0009
  have p0011 :=
    @g_n_3eqtr4i
      (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C)))
      (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))
        (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      (syn_cxp (syn_cun A B) C) (syn_cun (syn_cxp A C) (syn_cxp B C)) p0006 p0007 p0010
  exact p0011

@[expose]
noncomputable def g_brinxp2 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cin R (syn_cxp C D)) B)
        (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B))) :=
  by
  have p0000 := @g_ancom (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B)
  have p0001 := @g_brxp A B C D
  have p0002 :=
    @g_anbi1i (syn_wbr A (syn_cxp C D) B) (syn_wa (.classMem A C) (.classMem B D))
      (syn_wbr A R B) p0001
  have p0003 :=
    @g_bitri (syn_wa (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B))
      (syn_wa (syn_wbr A (syn_cxp C D) B) (syn_wbr A R B))
      (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B)) p0000 p0002
  have p0004 := @g_brin A B R (syn_cxp C D)
  have p0005 :=
    (Nominal.biimpRefl (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B)))
  have p0006 :=
    @g_n_3bitr4i (syn_wa (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B))
      (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B))
      (syn_wbr A (syn_cin R (syn_cxp C D)) B)
      (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B)) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_brinxp (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D))
        (syn_wb (syn_wbr A R B) (syn_wbr A (syn_cin R (syn_cxp C D)) B))) :=
  by
  have p0000 := @g_brinxp2 A B C D R
  have p0001 :=
    (Nominal.biimpRefl (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B)))
  have p0002 :=
    @g_bitri (syn_wbr A (syn_cin R (syn_cxp C D)) B)
      (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B))
      (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B)) p0000 p0001
  have p0003 :=
    @g_baibr (syn_wbr A (syn_cin R (syn_cxp C D)) B)
      (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B) p0002
  exact p0003

@[expose]
noncomputable def g_xp0r (A : Class) :
    Nominal.NPrf (.classEq (syn_cxp (syn_c0) A) (syn_c0)) :=
  by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : z ∉ ((syn_cxp (syn_c0) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_z_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_c0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    @g_elxp x y (.cv z) (syn_c0) A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @g_noel (.cv x)
  have p0002 :=
    @g_simprl (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.classMem (.cv x) (syn_c0))
      (.classMem (.cv y) A)
  have p0003 :=
    @g_mto
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A)))
      (.classMem (.cv x) (syn_c0)) p0001 p0002
  have p0004 :=
    @g_nex
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A)))
      y p0003
  have p0005 :=
    @g_nex
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A))))
      x p0004
  have p0006 := @g_noel (.cv z)
  have p0007 :=
    @g_n_2false
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A)))))
      (.classMem (.cv z) (syn_c0)) p0005 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cxp (syn_c0) A))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A)))))
      (.classMem (.cv z) (syn_c0)) p0000 p0007
  have p0009 := @g_eqriv z (syn_cxp (syn_c0) A) (syn_c0) dv_cache_0008 dv_cache_0009 p0008
  exact p0009

@[expose]
noncomputable def g_xpvv :
    Nominal.NPrf (.classEq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cxp (syn_cvv) (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_eqv x (syn_cxp (syn_cvv) (syn_cvv)) dv_cache_0001
  have p0001 := @g_opeq (.cv x)
  have p0002 := @g_vex x
  have p0003 := @g_proj1ex (.cv x) p0002
  have p0004 := @g_proj2ex (.cv x) p0002
  have p0005 := @g_opelxp (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mpbir2an
      (.classMem (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
        (syn_cxp (syn_cvv) (syn_cvv)))
      (.classMem (syn_cproj1 (.cv x)) (syn_cvv))
      (.classMem (syn_cproj2 (.cv x)) (syn_cvv)) p0003 p0004 p0005
  have p0007 :=
    @g_eqeltri (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
      (syn_cxp (syn_cvv) (syn_cvv)) p0001 p0006
  have p0008 :=
    @g_mpgbir (.classEq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv))
      (.classMem (.cv x) (syn_cxp (syn_cvv) (syn_cvv))) x p0000 p0007
  exact p0008

@[expose]
noncomputable def g_ssrel (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wss A B) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
              (.classMem (syn_cop (.cv x) (.cv y)) B))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_wss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          dv_A_y, dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv x) (syn_cproj1 (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cproj1 (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_z,
          not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.all y (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
            (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_ne_z, dv_x_y, dv_A_x, dv_B_x, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cproj2 (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_z,
          not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A)
          (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, dv_A_y, dv_B_y, or_false,
          not_false_eq_true])
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
  have dv_cache_0009 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((Wff.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
              (.classMem (syn_cop (.cv x) (.cv y)) B))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_ssel A B (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_alrimivv (syn_wss A B)
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))
      x y dv_cache_0001 dv_cache_0002 p0000
  have p0002 := @g_vex z
  have p0003 := @g_proj1ex (.cv z) p0002
  have p0004 := @g_opeq1 (.cv x) (syn_cproj1 (.cv z)) (.cv y)
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) (syn_cproj1 (.cv z))) (syn_cop (.cv x) (.cv y))
      (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A p0004
  have p0006 :=
    @g_eleq1d (.classEq (.cv x) (syn_cproj1 (.cv z))) (syn_cop (.cv x) (.cv y))
      (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B p0004
  have p0007 :=
    @g_imbi12d (.classEq (.cv x) (syn_cproj1 (.cv z)))
      (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) B)
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B) p0005 p0006
  have p0008 :=
    @g_albidv (.classEq (.cv x) (syn_cproj1 (.cv z)))
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))
      (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
        (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B))
      y dv_cache_0003 p0007
  have p0009 :=
    @g_spcv
      (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) B)))
      (.all y (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
          (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)))
      x (syn_cproj1 (.cv z)) dv_cache_0004 dv_cache_0005 p0003 p0008
  have p0010 := @g_proj2ex (.cv z) p0002
  have p0011 := @g_opeq2 (.cv y) (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z))
  have p0012 :=
    @g_eleq1d (.classEq (.cv y) (syn_cproj2 (.cv z)))
      (syn_cop (syn_cproj1 (.cv z)) (.cv y))
      (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A p0011
  have p0013 :=
    @g_eleq1d (.classEq (.cv y) (syn_cproj2 (.cv z)))
      (syn_cop (syn_cproj1 (.cv z)) (.cv y))
      (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B p0011
  have p0014 :=
    @g_imbi12d (.classEq (.cv y) (syn_cproj2 (.cv z)))
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A)
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B) p0012 p0013
  have p0015 :=
    @g_spcv
      (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
        (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B))
      (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A)
        (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B))
      y (syn_cproj2 (.cv z)) dv_cache_0006 dv_cache_0007 p0010 p0014
  have p0016 :=
    @g_syl
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      (.all y (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A)
          (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)))
      (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A)
        (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B))
      p0009 p0015
  have p0017 := @g_opeq (.cv z)
  have p0018 :=
    @g_eleq1i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A p0017
  have p0019 :=
    @g_eleq1i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B p0017
  have p0020 :=
    @g_n_3imtr4g
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A)
      (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B)
      (.classMem (.cv z) A) (.classMem (.cv z) B) p0016 p0018 p0019
  have p0021 :=
    @g_ssrdv
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      z A B dv_cache_0008 dv_cache_0009 dv_cache_0010 p0020
  have p0022 :=
    @g_impbii (syn_wss A B)
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      p0001 p0021
  exact p0022

@[expose]
noncomputable def g_eqrel (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
              (.classMem (syn_cop (.cv x) (.cv y)) B))))) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_ssrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_ssrel x y B A dv_cache_0003 dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0002 :=
    @g_anbi12i (syn_wss A B)
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      (syn_wss B A)
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) B)
            (.classMem (syn_cop (.cv x) (.cv y)) A))))
      p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 :=
    @g_n_2albiim (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) B) x y
  have p0005 :=
    @g_n_3bitr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
              (.classMem (syn_cop (.cv x) (.cv y)) B)))) (.all x (.all y
            (.imp (.classMem (syn_cop (.cv x) (.cv y)) B)
              (.classMem (syn_cop (.cv x) (.cv y)) A)))))
      (.classEq A B)
      (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_ssopr (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wss A B) (.all x (.all y (.all z
              (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ B.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : w ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0003 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0004 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0005 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 :
    x ∉
      ((Wff.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
          (.classMem (syn_cop (.cv w) (.cv z)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_x_z, dv_A_x, dv_B_x, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((Wff.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
          (.classMem (syn_cop (.cv w) (.cv z)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, dv_y_z, dv_A_y, dv_B_y, or_false,
          not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_cop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((Wff.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
          (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, fresh_w_not_A,
          fresh_w_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @g_ssrel w z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_alcom
      (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))
      w z
  have p0002 :=
    @g_bitri (syn_wss A B)
      (.all w (.all z (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
            (.classMem (syn_cop (.cv w) (.cv z)) B))))
      (.all z (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
            (.classMem (syn_cop (.cv w) (.cv z)) B))))
      p0000 p0001
  have p0003 := @g_vex w
  have p0004 := @g_opeqex x y (.cv w) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_a1bi (syn_wex x (syn_wex y (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))))
      (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))
      p0005
  have p0007 :=
    @g_n_19_23vv (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
      (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))
      x y dv_cache_0009 dv_cache_0010
  have p0008 :=
    @g_bitr4i
      (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))
      (.imp (syn_wex x (syn_wex y (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))))
        (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))
      (.all x (.all y (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
            (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
              (.classMem (syn_cop (.cv w) (.cv z)) B)))))
      p0006 p0007
  have p0009 :=
    @g_albii
      (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))
      (.all x (.all y (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
            (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
              (.classMem (syn_cop (.cv w) (.cv z)) B)))))
      w p0008
  have p0010 :=
    @g_alrot3
      (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
        (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))
      w x y
  have p0011 := @g_vex x
  have p0012 := @g_vex y
  have p0013 := @g_opex (.cv x) (.cv y) p0011 p0012
  have p0014 := @g_opeq1 (.cv w) (syn_cop (.cv x) (.cv y)) (.cv z)
  have p0015 :=
    @g_eleq1d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv w) (.cv z))
      (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A p0014
  have p0016 :=
    @g_eleq1d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv w) (.cv z))
      (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B p0014
  have p0017 :=
    @g_imbi12d (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
      (.classMem (syn_cop (.cv w) (.cv z)) A)
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
      (.classMem (syn_cop (.cv w) (.cv z)) B)
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B) p0015 p0016
  have p0018 :=
    @g_ceqsalv
      (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))
      (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))
      w (syn_cop (.cv x) (.cv y)) dv_cache_0011 dv_cache_0012 p0013 p0017
  have p0019 :=
    @g_n_2albii
      (.all w (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
          (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
            (.classMem (syn_cop (.cv w) (.cv z)) B))))
      (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))
      x y p0018
  have p0020 :=
    @g_n_3bitri
      (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
          (.classMem (syn_cop (.cv w) (.cv z)) B)))
      (.all w (.all x (.all y (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
              (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
                (.classMem (syn_cop (.cv w) (.cv z)) B))))))
      (.all x (.all y (.all w (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
              (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
                (.classMem (syn_cop (.cv w) (.cv z)) B))))))
      (.all x (.all y (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))
      p0009 p0010 p0019
  have p0021 :=
    @g_albii
      (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
          (.classMem (syn_cop (.cv w) (.cv z)) B)))
      (.all x (.all y (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))
      z p0020
  have p0022 :=
    @g_alrot3
      (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))
      z x y
  have p0023 :=
    @g_n_3bitri (syn_wss A B)
      (.all z (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A)
            (.classMem (syn_cop (.cv w) (.cv z)) B))))
      (.all z (.all x (.all y (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))
      (.all x (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))
      p0002 p0021 p0022
  exact p0023


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part064`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_eqopr (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (.all y (.all z
              (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))) :=
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
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0006 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_ssopr x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @g_ssopr x y z B A dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_anbi12i (syn_wss A B)
      (.all x (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))
      (syn_wss B A)
      (.all x (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)))))
      p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 :=
    @g_n_2albiim (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B) y z
  have p0005 :=
    @g_albii
      (.all y (.all z (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))
      (syn_wa (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))) (.all y (.all z
            (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)))))
      x p0004
  have p0006 :=
    @g_n_19_26
      (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))
      (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)
            (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))))
      x
  have p0007 :=
    @g_bitri
      (.all x (.all y (.all z (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))
      (.all x (syn_wa (.all y (.all z
              (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))) (.all y (.all z
              (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))))))
      (syn_wa (.all x (.all y (.all z
              (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))) (.all x (.all y
            (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))))))
      p0005 p0006
  have p0008 :=
    @g_n_3bitr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (.all x (.all y (.all z
              (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))) (.all x (.all y
            (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)
                (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))))))
      (.classEq A B)
      (.all x (.all y (.all z (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))
      p0002 p0003 p0007
  exact p0008

@[expose]
noncomputable def g_relssi (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_relssi_1 : Nominal.NPrf (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) B))) :
    Nominal.NPrf (syn_wss A B) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_ssrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := Nominal.gen hyp_relssi_1 y
  have p0002 :=
    @g_mpgbir (syn_wss A B)
      (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) B)))
      x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_relssdv (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_relssdv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B)))) :
    Nominal.NPrf (.imp ph (syn_wss A B)) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_alrimivv ph
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))
      x y dv_cache_0001 dv_cache_0002 hyp_relssdv_1
  have p0001 :=
    @g_ssrel x y A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_sylibr ph
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      (syn_wss A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqrelriv (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_eqrelriv_1 : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) B))) :
    Nominal.NPrf (.classEq A B) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_eqrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := Nominal.gen hyp_eqrelriv_1 y
  have p0002 :=
    @g_mpgbir (.classEq A B)
      (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) B)))
      x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqbrriv (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_eqbrriv_1 :
      Nominal.NPrf (syn_wb (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y)))) :
    Nominal.NPrf (.classEq A B) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y)))
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) B (.cv y)))
  have p0002 :=
    @g_n_3bitr3i (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)
      hyp_eqbrriv_1 p0000 p0001
  have p0003 :=
    @g_eqrelriv x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0002
  exact p0003

@[expose]
noncomputable def g_eqrelrdv (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_eqrelrdv_1 : Nominal.NPrf (.imp ph (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B)))) :
    Nominal.NPrf (.imp ph (.classEq A B)) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_alrimivv ph
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))
      x y dv_cache_0001 dv_cache_0002 hyp_eqrelrdv_1
  have p0001 :=
    @g_eqrel x y A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_sylibr ph
      (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) B))))
      (.classEq A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqoprriv (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_eqoprriv_1 : Nominal.NPrf
        (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
          (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))) :
    Nominal.NPrf (.classEq A B) :=
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
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0006 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_eqopr x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @g_gen2
      (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))
      y z hyp_eqoprriv_1
  have p0002 :=
    @g_mpgbir (.classEq A B)
      (.all y (.all z (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))
      x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_xpss12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss A B) (syn_wss C D)) (syn_wss (syn_cxp A C) (syn_cxp B D))) :=
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
  have dv_cache_0001 : x ∉ ((syn_wa (syn_wss A B) (syn_wss C D))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wa (syn_wss A B) (syn_wss C D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, fresh_y_not_D, or_false,
          not_false_eq_true])
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
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have dv_cache_0010 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0011 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have p0000 := @g_ssel A B (.cv x)
  have p0001 := @g_ssel C D (.cv y)
  have p0002 :=
    @g_im2anan9 (syn_wss A B) (.classMem (.cv x) A) (.classMem (.cv x) B) (syn_wss C D)
      (.classMem (.cv y) C) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @g_ssopab2dv (syn_wa (syn_wss A B) (syn_wss C D))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) D)) x y dv_cache_0001 dv_cache_0002
      p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B D
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0007
  have p0006 :=
    @g_n_3sstr4g (syn_wa (syn_wss A B) (syn_wss C D))
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) D))) (syn_cxp A C)
      (syn_cxp B D) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_xpss1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cxp A C) (syn_cxp B C))) :=
  by
  have p0000 := @g_ssid C
  have p0001 := @g_xpss12 A B C C
  have p0002 :=
    @g_mpan2 (syn_wss A B) (syn_wss C C) (syn_wss (syn_cxp A C) (syn_cxp B C)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_xpss2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cxp C A) (syn_cxp C B))) :=
  by
  have p0000 := @g_ssid C
  have p0001 := @g_xpss12 C C A B
  have p0002 :=
    @g_mpan (syn_wss C C) (syn_wss A B) (syn_wss (syn_cxp C A) (syn_cxp C B)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_br1st (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_br1st_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_c1st) B) (syn_wex x (.classEq A (syn_cop B (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) A)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv z) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show z ≠ x from (by exact fresh_z_ne_x))
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
  have dv_cache_0010 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wex x (.classEq A (syn_cop B (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wex x (.classEq A (syn_cop B (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_x, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_brex A B (syn_c1st)
  have p0001 :=
    @g_simpld (syn_wbr A (syn_c1st) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      p0000
  have p0002 := @g_vex x
  have p0003 := @g_opex B (.cv x) hyp_br1st_1 p0002
  have p0004 := @g_eleq1 A (syn_cop B (.cv x)) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cop B (.cv x))) (.classMem A (syn_cvv))
      (.classMem (syn_cop B (.cv x)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_exlimiv (.classEq A (syn_cop B (.cv x))) (.classMem A (syn_cvv)) x dv_cache_0001
      p0005
  have p0007 := @g_eqeq1 (.cv y) A (syn_cop (.cv z) (.cv x))
  have p0008 :=
    @g_exbidv (.classEq (.cv y) A) (.classEq (.cv y) (syn_cop (.cv z) (.cv x)))
      (.classEq A (syn_cop (.cv z) (.cv x))) x dv_cache_0002 p0007
  have p0009 := @g_opeq1 (.cv z) B (.cv x)
  have p0010 :=
    @g_eqeq2d (.classEq (.cv z) B) (syn_cop (.cv z) (.cv x)) (syn_cop B (.cv x)) A p0009
  have p0011 :=
    @g_exbidv (.classEq (.cv z) B) (.classEq A (syn_cop (.cv z) (.cv x)))
      (.classEq A (syn_cop B (.cv x))) x dv_cache_0003 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_1st y z x
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @g_brabg (syn_wex x (.classEq (.cv y) (syn_cop (.cv z) (.cv x))))
      (syn_wex x (.classEq A (syn_cop (.cv z) (.cv x))))
      (syn_wex x (.classEq A (syn_cop B (.cv x)))) y z A B (syn_cvv) (syn_cvv) (syn_c1st)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0004 p0008 p0011 p0012
  have p0014 :=
    @g_mpan2 (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr A (syn_c1st) B) (syn_wex x (.classEq A (syn_cop B (.cv x)))))
      hyp_br1st_1 p0013
  have p0015 :=
    @g_pm5_21nii (syn_wbr A (syn_c1st) B) (.classMem A (syn_cvv))
      (syn_wex x (.classEq A (syn_cop B (.cv x)))) p0001 p0006 p0014
  exact p0015

@[expose]
noncomputable def g_br2nd (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_br1st_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_c2nd) B) (syn_wex x (.classEq A (syn_cop (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) A)).fv :=
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
          Finset.mem_singleton, fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv z) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show z ≠ x from (by exact fresh_z_ne_x))
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
  have dv_cache_0010 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_wex x (.classEq A (syn_cop (.cv x) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, fresh_y_not_B, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wex x (.classEq A (syn_cop (.cv x) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_not_B, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_brex A B (syn_c2nd)
  have p0001 :=
    @g_simpld (syn_wbr A (syn_c2nd) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      p0000
  have p0002 := @g_vex x
  have p0003 := @g_opex (.cv x) B p0002 hyp_br1st_1
  have p0004 := @g_eleq1 A (syn_cop (.cv x) B) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cop (.cv x) B)) (.classMem A (syn_cvv))
      (.classMem (syn_cop (.cv x) B) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_exlimiv (.classEq A (syn_cop (.cv x) B)) (.classMem A (syn_cvv)) x dv_cache_0001
      p0005
  have p0007 := @g_eqeq1 (.cv y) A (syn_cop (.cv x) (.cv z))
  have p0008 :=
    @g_exbidv (.classEq (.cv y) A) (.classEq (.cv y) (syn_cop (.cv x) (.cv z)))
      (.classEq A (syn_cop (.cv x) (.cv z))) x dv_cache_0002 p0007
  have p0009 := @g_opeq2 (.cv z) B (.cv x)
  have p0010 :=
    @g_eqeq2d (.classEq (.cv z) B) (syn_cop (.cv x) (.cv z)) (syn_cop (.cv x) B) A p0009
  have p0011 :=
    @g_exbidv (.classEq (.cv z) B) (.classEq A (syn_cop (.cv x) (.cv z)))
      (.classEq A (syn_cop (.cv x) B)) x dv_cache_0003 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_2nd y z x
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @g_brabg (syn_wex x (.classEq (.cv y) (syn_cop (.cv x) (.cv z))))
      (syn_wex x (.classEq A (syn_cop (.cv x) (.cv z))))
      (syn_wex x (.classEq A (syn_cop (.cv x) B))) y z A B (syn_cvv) (syn_cvv) (syn_c2nd)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0004 p0008 p0011 p0012
  have p0014 :=
    @g_mpan2 (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr A (syn_c2nd) B) (syn_wex x (.classEq A (syn_cop (.cv x) B))))
      hyp_br1st_1 p0013
  have p0015 :=
    @g_pm5_21nii (syn_wbr A (syn_c2nd) B) (.classMem A (syn_cvv))
      (syn_wex x (.classEq A (syn_cop (.cv x) B))) p0001 p0006 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
