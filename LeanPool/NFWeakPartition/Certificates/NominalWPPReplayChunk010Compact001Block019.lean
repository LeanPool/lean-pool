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

/-- Checked nominal proof certificate identified upstream as `g_elima`. -/
@[expose]
noncomputable def gElima (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B C)) (synWrex x C (synWbr (.cv x) B A))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem A (synCvv))).fv := by
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
  have dv_cache_0009 : y ∉ ((synWrex x C (synWbr (.cv x) B A))).fv :=
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
  have p0000 := @gElex A (synCima B C)
  have p0001 := @gBrex (.cv x) A B
  have p0002 :=
    @gSimprd (synWbr (.cv x) B A) (.classMem (.cv x) (synCvv)) (.classMem A (synCvv))
      p0001
  have p0003 :=
    @gRexlimivw (synWbr (.cv x) B A) (.classMem A (synCvv)) x C dv_cache_0001 p0002
  have p0004 := @gBreq2 (.cv y) A (.cv x) B
  have p0005 :=
    @gRexbidv (.classEq (.cv y) A) (synWbr (.cv x) B (.cv y)) (synWbr (.cv x) B A) x C
      dv_cache_0002 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x B C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @gElab2g (synWrex x C (synWbr (.cv x) B (.cv y)))
      (synWrex x C (synWbr (.cv x) B A)) y A (synCima B C) (synCvv) dv_cache_0008
      dv_cache_0009 p0005 p0006
  have p0008 :=
    @gPm521nii (.classMem A (synCima B C)) (.classMem A (synCvv))
      (synWrex x C (synWbr (.cv x) B A)) p0000 p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_elima2`. -/
@[expose]
noncomputable def gElima2 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B C))
        (synWex x (synWa (.classMem (.cv x) C) (synWbr (.cv x) B A)))) :=
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
  have p0000 := @gElima x A B C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (synWrex x C (synWbr (.cv x) B A)))
  have p0002 :=
    @gBitri (.classMem A (synCima B C)) (synWrex x C (synWbr (.cv x) B A))
      (synWex x (synWa (.classMem (.cv x) C) (synWbr (.cv x) B A))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elima3`. -/
@[expose]
noncomputable def gElima3 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B C))
        (synWex x (synWa (.classMem (.cv x) C) (.classMem (synCop (.cv x) A) B)))) :=
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
  have p0000 := @gElima x A B C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) B A))
  have p0002 :=
    @gRexbii (synWbr (.cv x) B A) (.classMem (synCop (.cv x) A) B) x C p0001
  have p0003 :=
    @gBitri (.classMem A (synCima B C)) (synWrex x C (synWbr (.cv x) B A))
      (synWrex x C (.classMem (synCop (.cv x) A) B)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWrex x C (.classMem (synCop (.cv x) A) B)))
  have p0005 :=
    @gBitri (.classMem A (synCima B C)) (synWrex x C (.classMem (synCop (.cv x) A) B))
      (synWex x (synWa (.classMem (.cv x) C) (.classMem (synCop (.cv x) A) B))) p0003
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_brssetg`. -/
@[expose]
noncomputable def gBrssetg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (synWbr A (synCsset) B) (synWss A B))) :=
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
  have dv_cache_0006 : x ∉ ((synWss A B)).fv :=
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
  have dv_cache_0007 : y ∉ ((synWss A B)).fv :=
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
  have p0000 := @gSseq1 (.cv x) A (.cv y)
  have p0001 := @gSseq2 (.cv y) B A
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSset x y
      dv_cache_0001
  have p0003 :=
    @gBrabg (synWss (.cv x) (.cv y)) (synWss A (.cv y)) (synWss A B) x y A B V W
      (synCsset) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_brsset`. -/
@[expose]
noncomputable def gBrsset (A : Class) (B : Class)
    (hyp_brsset_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brsset_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr A (synCsset) B) (synWss A B)) :=
  by
  have p0000 := @gBrssetg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr A (synCsset) B) (synWss A B)) hyp_brsset_1 hyp_brsset_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_brssetsn`. -/
@[expose]
noncomputable def gBrssetsn (A : Class) (B : Class)
    (hyp_brssetsn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brssetsn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr (synCsn A) (synCsset) B) (.classMem A B)) :=
  by
  have p0000 := @gSnex A
  have p0001 := @gBrsset (synCsn A) B p0000 hyp_brssetsn_2
  have p0002 := @gSnss A B hyp_brssetsn_1
  have p0003 :=
    @gBitr4i (synWbr (synCsn A) (synCsset) B) (synWss (synCsn A) B) (.classMem A B)
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_opelssetsn`. -/
@[expose]
noncomputable def gOpelssetsn (A : Class) (B : Class)
    (hyp_brssetsn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brssetsn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn A) B) (synCsset)) (.classMem A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr (synCsn A) (synCsset) B))
  have p0001 := @gBrssetsn A B hyp_brssetsn_1 hyp_brssetsn_2
  have p0002 :=
    @gBitr3i (.classMem (synCop (synCsn A) B) (synCsset))
      (synWbr (synCsn A) (synCsset) B) (.classMem A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_brsi`. -/
@[expose]
noncomputable def gBrsi (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWbr A (synCsi R) B) (synWex x (synWex y
            (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
              (synWbr (.cv x) R (.cv y)))))) :=
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
    x ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv := by
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
    y ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv :=
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
      ((synWex x (synWex y
            (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
              (synWbr (.cv x) R (.cv y)))))).fv :=
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
      ((synWex x (synWex y
            (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
              (synWbr (.cv x) R (.cv y)))))).fv :=
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
  have p0000 := @gBrex A B (synCsi R)
  have p0001 := @gSnex (.cv x)
  have p0002 := @gSnex (.cv y)
  have p0003 :=
    @gPm32i (.classMem (synCsn (.cv x)) (synCvv))
      (.classMem (synCsn (.cv y)) (synCvv)) p0001 p0002
  have p0004 := @gEleq1 A (synCsn (.cv x)) (synCvv)
  have p0005 := @gEleq1 B (synCsn (.cv y)) (synCvv)
  have p0006 :=
    @gBi2anan9 (.classEq A (synCsn (.cv x))) (.classMem A (synCvv))
      (.classMem (synCsn (.cv x)) (synCvv)) (.classEq B (synCsn (.cv y)))
      (.classMem B (synCvv)) (.classMem (synCsn (.cv y)) (synCvv)) p0004 p0005
  have p0007 :=
    @gMpbiri (synWa (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (.classMem (synCsn (.cv x)) (synCvv)) (.classMem (synCsn (.cv y)) (synCvv)))
      p0003 p0006
  have p0008 :=
    @gN3adant3 (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) (synWbr (.cv x) R (.cv y))
      p0007
  have p0009 :=
    @gExlimivv
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) x y dv_cache_0001
      dv_cache_0002 p0008
  have p0010 := @gEqeq1 (.cv z) A (synCsn (.cv x))
  have p0011 :=
    @gN3anbi1d (.classEq (.cv z) A) (.classEq (.cv z) (synCsn (.cv x)))
      (.classEq A (synCsn (.cv x))) (.classEq (.cv w) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0010
  have p0012 :=
    @gN2exbidv (.classEq (.cv z) A)
      (synW3a (.classEq (.cv z) (synCsn (.cv x))) (.classEq (.cv w) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv w) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      x y dv_cache_0003 dv_cache_0004 p0011
  have p0013 := @gEqeq1 (.cv w) B (synCsn (.cv y))
  have p0014 :=
    @gN3anbi2d (.classEq (.cv w) B) (.classEq (.cv w) (synCsn (.cv y)))
      (.classEq B (synCsn (.cv y))) (.classEq A (synCsn (.cv x)))
      (synWbr (.cv x) R (.cv y)) p0013
  have p0015 :=
    @gN2exbidv (.classEq (.cv w) B)
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv w) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      x y dv_cache_0005 dv_cache_0006 p0014
  have p0016 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSi z w x y R
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0017 :=
    @gBrabg
      (synWex x (synWex y (synW3a (.classEq (.cv z) (synCsn (.cv x)))
            (.classEq (.cv w) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWex y
          (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv w) (synCsn (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWex y
          (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      z w A B (synCvv) (synCvv) (synCsi R) dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0014 p0012 p0015 p0016
  have p0018 :=
    @gPm521nii (synWbr A (synCsi R) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex x (synWex y
          (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      p0000 p0009 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_xpeq1`. -/
@[expose]
noncomputable def gXpeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCxp A C) (synCxp B C))) :=
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
  have p0000 := @gEleq2 A B (.cv x)
  have p0001 :=
    @gAnbi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv y) C) p0000
  have p0002 :=
    @gOpabbidv (.classEq A B) (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y dv_cache_0001 dv_cache_0002
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y B C
      dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @gN3eqtr4g (.classEq A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))) (synCxp A C)
      (synCxp B C) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_xpeq2`. -/
@[expose]
noncomputable def gXpeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCxp C A) (synCxp C B))) :=
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
  have p0000 := @gEleq2 A B (.cv y)
  have p0001 :=
    @gAnbi2d (.classEq A B) (.classMem (.cv y) A) (.classMem (.cv y) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @gOpabbidv (.classEq A B) (synWa (.classMem (.cv x) C) (.classMem (.cv y) A))
      (synWa (.classMem (.cv x) C) (.classMem (.cv y) B)) x y dv_cache_0001 dv_cache_0002
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y C A
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y C B
      dv_cache_0003 dv_cache_0004 dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0005 :=
    @gN3eqtr4g (.classEq A B)
      (synCopab x y (synWa (.classMem (.cv x) C) (.classMem (.cv y) A)))
      (synCopab x y (synWa (.classMem (.cv x) C) (.classMem (.cv y) B))) (synCxp C A)
      (synCxp C B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elxp`. -/
@[expose]
noncomputable def gElxp (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCxp B C)) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y B C
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gEleq2i (synCxp B C)
      (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))) A p0000
  have p0002 :=
    @gElopab (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y A dv_cache_0006
      dv_cache_0007
  have p0003 :=
    @gBitri (.classMem A (synCxp B C))
      (.classMem A (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elxp2`. -/
@[expose]
noncomputable def gElxp2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCxp B C))
        (synWrex x B (synWrex y C (.classEq A (synCop (.cv x) (.cv y)))))) :=
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
    (Nominal.biimpRefl (synWrex y C
        (synWa (.classMem (.cv x) B) (.classEq A (synCop (.cv x) (.cv y))))))
  have p0001 :=
    @gR1942v (.classMem (.cv x) B) (.classEq A (synCop (.cv x) (.cv y))) y C
      dv_cache_0001
  have p0002 :=
    @gAn13 (.classMem (.cv y) C) (.classMem (.cv x) B)
      (.classEq A (synCop (.cv x) (.cv y)))
  have p0003 :=
    @gExbii
      (synWa (.classMem (.cv y) C)
        (synWa (.classMem (.cv x) B) (.classEq A (synCop (.cv x) (.cv y)))))
      (synWa (.classEq A (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      y p0002
  have p0004 :=
    @gN3bitr3i
      (synWrex y C (synWa (.classMem (.cv x) B) (.classEq A (synCop (.cv x) (.cv y)))))
      (synWex y (synWa (.classMem (.cv y) C)
          (synWa (.classMem (.cv x) B) (.classEq A (synCop (.cv x) (.cv y))))))
      (synWa (.classMem (.cv x) B) (synWrex y C (.classEq A (synCop (.cv x) (.cv y)))))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      p0000 p0001 p0003
  have p0005 :=
    @gExbii
      (synWa (.classMem (.cv x) B) (synWrex y C (.classEq A (synCop (.cv x) (.cv y)))))
      (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      x p0004
  have p0006 :=
    (Nominal.biimpRefl (synWrex x B (synWrex y C (.classEq A (synCop (.cv x) (.cv y))))))
  have p0007 :=
    @gElxp x y A B C dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 :=
    @gN3bitr4ri
      (synWex x (synWa (.classMem (.cv x) B)
          (synWrex y C (.classEq A (synCop (.cv x) (.cv y))))))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      (synWrex x B (synWrex y C (.classEq A (synCop (.cv x) (.cv y)))))
      (.classMem A (synCxp B C)) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_xpeq12`. -/
@[expose]
noncomputable def gXpeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCxp A C) (synCxp B D))) :=
  by
  have p0000 := @gXpeq1 A B C
  have p0001 := @gXpeq2 C D B
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCxp A C) (synCxp B C) (synCxp B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_xpeq1i`. -/
@[expose]
noncomputable def gXpeq1i (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCxp A C) (synCxp B C)) :=
  by
  have p0000 := @gXpeq1 A B C
  have p0001 := Nominal.mp hyp_xpeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpeq2i`. -/
@[expose]
noncomputable def gXpeq2i (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCxp C A) (synCxp C B)) :=
  by
  have p0000 := @gXpeq2 A B C
  have p0001 := Nominal.mp hyp_xpeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpeq12i`. -/
@[expose]
noncomputable def gXpeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_xpeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCxp A C) (synCxp B D)) :=
  by
  have p0000 := @gXpeq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (.classEq (synCxp A C) (synCxp B D))
      hyp_xpeq12i_1 hyp_xpeq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpeq1d`. -/
@[expose]
noncomputable def gXpeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCxp A C) (synCxp B C))) :=
  by
  have p0000 := @gXpeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCxp A C) (synCxp B C)) hyp_xpeq1d_1 p0000
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

/-- Checked nominal proof certificate identified upstream as `g_xpeq2d`. -/
@[expose]
noncomputable def gXpeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_xpeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCxp C A) (synCxp C B))) :=
  by
  have p0000 := @gXpeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCxp C A) (synCxp C B)) hyp_xpeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpeq12d`. -/
@[expose]
noncomputable def gXpeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_xpeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCxp A C) (synCxp B D))) :=
  by
  have p0000 := @gXpeq12 A B C D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (.classEq (synCxp A C) (synCxp B D))
      hyp_xpeq1d_1 hyp_xpeq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfxp`. -/
@[expose]
noncomputable def gNfxp (x : Var) (A : Class) (B : Class)
    (hyp_nfxp_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfxp_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnfc x (synCxp A B)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp y z A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gNfcri x y A dv_cache_0006 hyp_nfxp_1
  have p0002 := @gNfcri x z B dv_cache_0007 hyp_nfxp_2
  have p0003 := @gNfan (.classMem (.cv y) A) (.classMem (.cv z) B) x p0001 p0002
  have p0004 :=
    @gNfopab (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) y z x dv_cache_0008
      dv_cache_0009 p0003
  have p0005 :=
    @gNfcxfr x (synCxp A B)
      (synCopab y z (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_opelxp`. -/
@[expose]
noncomputable def gOpelxp (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (synWb (.classMem (synCop A B) (synCxp C D))
        (synWa (.classMem A C) (.classMem B D))) :=
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
  have dv_cache_0001 : x ∉ ((synCop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCop A B)).fv :=
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
  have dv_cache_0010 : y ∉ ((synWa (.classEq (.cv x) A) (.classMem (.cv x) C))).fv :=
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
  have dv_cache_0011 : x ∉ ((synWa (.classEq (.cv y) B) (.classMem (.cv y) D))).fv :=
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
  have p0000 := @gEqcom (synCop A B) (synCop (.cv x) (.cv y))
  have p0001 := @gOpth (.cv x) (.cv y) A B
  have p0002 :=
    @gBitri (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0000 p0001
  have p0003 :=
    @gAnbi1i (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0002
  have p0004 :=
    @gAn4 (.classEq (.cv x) A) (.classEq (.cv y) B) (.classMem (.cv x) C)
      (.classMem (.cv y) D)
  have p0005 :=
    @gBitri
      (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (synWa (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (synWa (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))
        (synWa (.classEq (.cv y) B) (.classMem (.cv y) D)))
      p0003 p0004
  have p0006 :=
    @gN2exbii
      (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (synWa (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))
        (synWa (.classEq (.cv y) B) (.classMem (.cv y) D)))
      x y p0005
  have p0007 :=
    @gElxp x y (synCop A B) C D dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A C
      dv_cache_0008 dv_cache_0003)
  have p0009 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y B D
      dv_cache_0009 dv_cache_0006)
  have p0010 :=
    @gAnbi12i (.classMem A C)
      (synWex x (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))) (.classMem B D)
      (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv y) D))) p0008 p0009
  have p0011 :=
    @gEeanv (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))
      (synWa (.classEq (.cv y) B) (.classMem (.cv y) D)) x y dv_cache_0010 dv_cache_0011
  have p0012 :=
    @gBitr4i (synWa (.classMem A C) (.classMem B D))
      (synWa (synWex x (synWa (.classEq (.cv x) A) (.classMem (.cv x) C)))
        (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv y) D))))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))
            (synWa (.classEq (.cv y) B) (.classMem (.cv y) D)))))
      p0010 p0011
  have p0013 :=
    @gN3bitr4i
      (synWex x (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))
            (synWa (.classEq (.cv y) B) (.classMem (.cv y) D)))))
      (.classMem (synCop A B) (synCxp C D)) (synWa (.classMem A C) (.classMem B D))
      p0006 p0007 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_brxp`. -/
@[expose]
noncomputable def gBrxp (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCxp C D) B) (synWa (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr A (synCxp C D) B))
  have p0001 := @gOpelxp A B C D
  have p0002 :=
    @gBitri (synWbr A (synCxp C D) B) (.classMem (synCop A B) (synCxp C D))
      (synWa (.classMem A C) (.classMem B D)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fconstopab`. -/
@[expose]
noncomputable def gFconstopab (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCxp A (synCsn B))
        (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))) :=
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
  have dv_cache_0003 : x ∉ ((synCsn B)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCsn B)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A (synCsn B)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn y B dv_cache_0006
  have p0002 := @gEqabri (.classEq (.cv y) B) y (synCsn B) p0001
  have p0003 :=
    @gAnbi2i (.classMem (.cv y) (synCsn B)) (.classEq (.cv y) B) (.classMem (.cv x) A)
      p0002
  have p0004 :=
    @gOpabbii (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCsn B)))
      (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y p0003
  have p0005 :=
    @gEqtri (synCxp A (synCsn B))
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCsn B))))
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_xpiundir`. -/
@[expose]
noncomputable def gXpiundir (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (.classEq (synCxp (synCiun x A B) C) (synCiun x A (synCxp B C))) :=
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
    x ∉ ((synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))).fv :=
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
  have dv_cache_0012 : y ∉ ((synCiun x A B)).fv :=
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
  have dv_cache_0013 : w ∉ ((synCiun x A B)).fv :=
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
  have dv_cache_0015 : z ∉ ((synCxp (synCiun x A B) C)).fv :=
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
  have dv_cache_0016 : z ∉ ((synCiun x A (synCxp B C))).fv :=
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
    @gRexcom4
      (synWa (.classMem (.cv y) B) (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      x y A dv_cache_0001 dv_cache_0002
  have p0001 :=
    (Nominal.biimpRefl
      (synWrex y B (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
  have p0002 :=
    @gRexbii (synWrex y B (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      (synWex y (synWa (.classMem (.cv y) B)
          (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      x A p0001
  have p0003 := @gEliun x (.cv y) A B dv_cache_0003
  have p0004 :=
    @gAnbi1i (.classMem (.cv y) (synCiun x A B)) (synWrex x A (.classMem (.cv y) B))
      (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))) p0003
  have p0005 :=
    @gR1941v (.classMem (.cv y) B)
      (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))) x A dv_cache_0004
  have p0006 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCiun x A B))
        (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      (synWa (synWrex x A (.classMem (.cv y) B))
        (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      (synWrex x A (synWa (.classMem (.cv y) B)
          (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      p0004 p0005
  have p0007 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCiun x A B))
        (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      (synWrex x A (synWa (.classMem (.cv y) B)
          (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      y p0006
  have p0008 :=
    @gN3bitr4ri
      (synWrex x A (synWex y (synWa (.classMem (.cv y) B)
            (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))))
      (synWex y (synWrex x A (synWa (.classMem (.cv y) B)
            (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))))
      (synWrex x A (synWrex y B (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      (synWex y (synWa (.classMem (.cv y) (synCiun x A B))
          (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      p0000 p0002 p0007
  have p0009 :=
    (Nominal.biimpRefl (synWrex y (synCiun x A B)
        (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
  have p0010 :=
    @gElxp2 y w (.cv z) B C dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0011 :=
    @gRexbii (.classMem (.cv z) (synCxp B C))
      (synWrex y B (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))) x A p0010
  have p0012 :=
    @gN3bitr4i
      (synWex y (synWa (.classMem (.cv y) (synCiun x A B))
          (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      (synWrex x A (synWrex y B (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w))))))
      (synWrex y (synCiun x A B) (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      (synWrex x A (.classMem (.cv z) (synCxp B C))) p0008 p0009 p0011
  have p0013 :=
    @gElxp2 y w (.cv z) (synCiun x A B) C dv_cache_0005 dv_cache_0006 dv_cache_0012
      dv_cache_0013 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0014 := @gEliun x (.cv z) A (synCxp B C) dv_cache_0014
  have p0015 :=
    @gN3bitr4i
      (synWrex y (synCiun x A B) (synWrex w C (.classEq (.cv z) (synCop (.cv y) (.cv w)))))
      (synWrex x A (.classMem (.cv z) (synCxp B C)))
      (.classMem (.cv z) (synCxp (synCiun x A B) C))
      (.classMem (.cv z) (synCiun x A (synCxp B C))) p0012 p0013 p0014
  have p0016 :=
    @gEqriv z (synCxp (synCiun x A B) C) (synCiun x A (synCxp B C)) dv_cache_0015
      dv_cache_0016 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_iunxpconst`. -/
@[expose]
noncomputable def gIunxpconst (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.classEq (synCiun x A (synCxp (synCsn (.cv x)) B)) (synCxp A B)) :=
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
  have p0000 := @gXpiundir x A (synCsn (.cv x)) B dv_cache_0001
  have p0001 := @gIunid x A dv_cache_0002
  have p0002 := @gXpeq1i (synCiun x A (synCsn (.cv x))) A B p0001
  have p0003 :=
    @gEqtr3i (synCxp (synCiun x A (synCsn (.cv x))) B)
      (synCiun x A (synCxp (synCsn (.cv x)) B)) (synCxp A B) p0000 p0002
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

/-- Checked nominal proof certificate identified upstream as `g_opeliunxp`. -/
@[expose]
noncomputable def gOpeliunxp (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B)))
        (synWa (.classMem (.cv x) A) (.classMem C B))) :=
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
      ((synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCxp (synCsn (.cv x)) B)))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCsn (.cv z))).fv :=
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
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv y) (synCop (.cv x) C))).fv :=
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
  have dv_cache_0008 : y ∉ ((synCxp (synCsn (.cv x)) B)).fv :=
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
  have dv_cache_0009 : y ∉ ((synCop (.cv x) C)).fv :=
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
      ((synWex z (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem (synCop (.cv x) C)
              (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))).fv :=
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
  have dv_cache_0012 : z ∉ ((synWa (.classMem (.cv x) A) (.classMem C B))).fv :=
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
  have p0000 := @gElex (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B))
  have p0001 := @gOpexb (.cv x) C
  have p0002 :=
    @gSimprbi (.classMem (synCop (.cv x) C) (synCvv)) (.classMem (.cv x) (synCvv))
      (.classMem C (synCvv)) p0001
  have p0003 :=
    @gSyl (.classMem (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (.classMem (synCop (.cv x) C) (synCvv)) (.classMem C (synCvv)) p0000 p0002
  have p0004 := @gElex C B
  have p0005 :=
    @gAdantl (.classMem C B) (.classMem C (synCvv)) (.classMem (.cv x) A) p0004
  have p0006 := @gVex x
  have p0007 := @gOpexg (.cv x) C (synCvv) (synCvv)
  have p0008 :=
    @gMpan (.classMem (.cv x) (synCvv)) (.classMem C (synCvv))
      (.classMem (synCop (.cv x) C) (synCvv)) p0006 p0007
  have p0009 :=
    (Nominal.biimpRefl (synWrex x A (.classMem (.cv y) (synCxp (synCsn (.cv x)) B))))
  have p0010 :=
    @gNfv
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCxp (synCsn (.cv x)) B))) z
      dv_cache_0001
  have p0011 := @gNfs1v (.classMem (.cv x) A) x z dv_cache_0002
  have p0012 := @gNfcv x (synCsn (.cv z)) dv_cache_0003
  have p0013 := @gNfcsb1v x (.cv z) B dv_cache_0004
  have p0014 := @gNfxp x (synCsn (.cv z)) (synCsb (.cv z) x B) p0012 p0013
  have p0015 :=
    @gNfcri x y (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)) dv_cache_0005 p0014
  have p0016 :=
    @gNfan (synWsb z x (.classMem (.cv x) A))
      (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) x p0011 p0015
  have p0017 := @gSbequ12 (.classMem (.cv x) A) x z
  have p0018 := @gSneq (.cv x) (.cv z)
  have p0019 := @gCsbeq1a x (.cv z) B
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (synCsn (.cv x)) (synCsn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0020_e01_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq B (synCsb (.cv z) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsb synWsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gXpeq12d (.objEq x z) (synCsn (.cv x)) (synCsn (.cv z)) B (synCsb (.cv z) x B)
      p0020_e00_recanon p0020_e01_recanon
  have p0021 :=
    @gEleq2d (.objEq x z) (synCxp (synCsn (.cv x)) B)
      (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)) (.cv y) p0020
  have p0022 :=
    @gAnbi12d (.objEq x z) (.classMem (.cv x) A) (synWsb z x (.classMem (.cv x) A))
      (.classMem (.cv y) (synCxp (synCsn (.cv x)) B))
      (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) p0017 p0021
  have p0023 :=
    @gCbvex
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCxp (synCsn (.cv x)) B)))
      (synWa (synWsb z x (.classMem (.cv x) A))
        (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))))
      x z p0010 p0016 p0022
  have p0024 :=
    @gBitri (synWrex x A (.classMem (.cv y) (synCxp (synCsn (.cv x)) B)))
      (synWex x
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCxp (synCsn (.cv x)) B))))
      (synWex z (synWa (synWsb z x (.classMem (.cv x) A))
          (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))
      p0009 p0023
  have p0025 :=
    @gEleq1 (.cv y) (synCop (.cv x) C) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))
  have p0026 :=
    @gAnbi2d (.classEq (.cv y) (synCop (.cv x) C))
      (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))
      (.classMem (synCop (.cv x) C) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))
      (synWsb z x (.classMem (.cv x) A)) p0025
  have p0027 :=
    @gExbidv (.classEq (.cv y) (synCop (.cv x) C))
      (synWa (synWsb z x (.classMem (.cv x) A))
        (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))))
      (synWa (synWsb z x (.classMem (.cv x) A))
        (.classMem (synCop (.cv x) C) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))))
      z dv_cache_0006 p0026
  have p0028 :=
    @gSyl5bb (synWrex x A (.classMem (.cv y) (synCxp (synCsn (.cv x)) B)))
      (synWex z (synWa (synWsb z x (.classMem (.cv x) A))
          (.classMem (.cv y) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))
      (.classEq (.cv y) (synCop (.cv x) C))
      (synWex z (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem (synCop (.cv x) C)
            (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))
      p0024 p0027
  have p0029 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIun x y A
      (synCxp (synCsn (.cv x)) B) dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0030 :=
    @gElab2g (synWrex x A (.classMem (.cv y) (synCxp (synCsn (.cv x)) B)))
      (synWex z (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem (synCop (.cv x) C)
            (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))
      y (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B)) (synCvv)
      dv_cache_0009 dv_cache_0010 p0028 p0029
  have p0031 :=
    @gSyl (.classMem C (synCvv)) (.classMem (synCop (.cv x) C) (synCvv))
      (synWb (.classMem (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B)))
        (synWex z (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem (synCop (.cv x) C)
              (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))))))
      p0008 p0030
  have p0032 := @gOpelxp (.cv x) C (synCsn (.cv z)) (synCsb (.cv z) x B)
  have p0033 :=
    @gAnbi2i
      (.classMem (synCop (.cv x) C) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))
      (synWa (.classMem (.cv x) (synCsn (.cv z))) (.classMem C (synCsb (.cv z) x B)))
      (synWsb z x (.classMem (.cv x) A)) p0032
  have p0034 :=
    @gAn12 (synWsb z x (.classMem (.cv x) A)) (.classMem (.cv x) (synCsn (.cv z)))
      (.classMem C (synCsb (.cv z) x B))
  have p0035 := @gElsn x (.cv z) dv_cache_0004
  have p0036 := @gEqucom x z
  have p0037_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCsn (.cv z))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
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
    @gBitri (.classMem (.cv x) (synCsn (.cv z))) (.objEq x z) (.objEq z x)
      p0037_e00_recanon p0036
  have p0038 :=
    @gAnbi1i (.classMem (.cv x) (synCsn (.cv z))) (.objEq z x)
      (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem C (synCsb (.cv z) x B)))
      p0037
  have p0039 :=
    @gN3bitri
      (synWa (synWsb z x (.classMem (.cv x) A))
        (.classMem (synCop (.cv x) C) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))))
      (synWa (synWsb z x (.classMem (.cv x) A)) (synWa (.classMem (.cv x) (synCsn (.cv z)))
          (.classMem C (synCsb (.cv z) x B))))
      (synWa (.classMem (.cv x) (synCsn (.cv z)))
        (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem C (synCsb (.cv z) x B))))
      (synWa (.objEq z x)
        (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem C (synCsb (.cv z) x B))))
      p0033 p0034 p0038
  have p0040 :=
    @gExbii
      (synWa (synWsb z x (.classMem (.cv x) A))
        (.classMem (synCop (.cv x) C) (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))))
      (synWa (.objEq z x)
        (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem C (synCsb (.cv z) x B))))
      z p0039
  have p0041 := @gSbequ12r (.classMem (.cv x) A) z x
  have p0042_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq B (synCsb (.cv z) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsb synWsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0042 := @gEqucoms (.classEq B (synCsb (.cv z) x B)) x z p0042_e00_recanon
  have p0043 := @gEqcomd (.objEq z x) B (synCsb (.cv z) x B) p0042
  have p0044 := @gEleq2d (.objEq z x) (synCsb (.cv z) x B) B C p0043
  have p0045 :=
    @gAnbi12d (.objEq z x) (synWsb z x (.classMem (.cv x) A)) (.classMem (.cv x) A)
      (.classMem C (synCsb (.cv z) x B)) (.classMem C B) p0041 p0044
  have p0046_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (synWb
          (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem C (synCsb (.cv z) x B)))
          (synWa (.classMem (.cv x) A) (.classMem C B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWsb synCsb synWsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @gCeqsexv
      (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem C (synCsb (.cv z) x B)))
      (synWa (.classMem (.cv x) A) (.classMem C B)) z (.cv x) dv_cache_0011 dv_cache_0012
      p0006 p0046_e01_recanon
  have p0047_e01_recanon :
    Nominal.NPrf
      (synWb (synWex z (synWa (.objEq z x) (synWa (synWsb z x (.classMem (.cv x) A))
              (.classMem C (synCsb (.cv z) x B)))))
        (synWa (.classMem (.cv x) A) (.classMem C B))) :=
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
      p0046
  have p0047 :=
    @gBitri
      (synWex z (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem (synCop (.cv x) C)
            (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))
      (synWex z (synWa (.objEq z x) (synWa (synWsb z x (.classMem (.cv x) A))
            (.classMem C (synCsb (.cv z) x B)))))
      (synWa (.classMem (.cv x) A) (.classMem C B)) p0040 p0047_e01_recanon
  have p0048 :=
    @gSyl6bb (.classMem C (synCvv))
      (.classMem (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (synWex z (synWa (synWsb z x (.classMem (.cv x) A)) (.classMem (synCop (.cv x) C)
            (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))))
      (synWa (.classMem (.cv x) A) (.classMem C B)) p0031 p0047
  have p0049 :=
    @gPm521nii
      (.classMem (synCop (.cv x) C) (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (.classMem C (synCvv)) (synWa (.classMem (.cv x) A) (.classMem C B)) p0003 p0005
      p0048
  exact p0049

/-- Checked nominal proof certificate identified upstream as `g_eliunxp`. -/
@[expose]
noncomputable def gEliunxp (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))) (synWex x (synWex y
            (synWa (.classEq C (synCop (.cv x) (.cv y)))
              (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))))) :=
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
    y ∉ ((Wff.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))).fv :=
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
  have p0000 := @gElex C (synCiun x A (synCxp (synCsn (.cv x)) B))
  have p0001 :=
    @gPm471ri (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (.classMem C (synCvv)) p0000
  have p0002 := @gOpeqexb x y C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @gAnbi1i (.classMem C (synCvv))
      (synWex x (synWex y (.classEq C (synCop (.cv x) (.cv y)))))
      (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))) p0002
  have p0004 :=
    @gBitri (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (synWa (.classMem C (synCvv))
        (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))))
      (synWa (synWex x (synWex y (.classEq C (synCop (.cv x) (.cv y)))))
        (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))))
      p0001 p0003
  have p0005 := @gNfiu1 x A (synCxp (synCsn (.cv x)) B)
  have p0006 :=
    @gNfel2 x C (synCiun x A (synCxp (synCsn (.cv x)) B)) dv_cache_0001 p0005
  have p0007 :=
    @gN1941 (synWex y (.classEq C (synCop (.cv x) (.cv y))))
      (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))) x p0006
  have p0008 :=
    @gN1941v (.classEq C (synCop (.cv x) (.cv y)))
      (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))) y dv_cache_0004
  have p0009 :=
    @gEleq1 C (synCop (.cv x) (.cv y)) (synCiun x A (synCxp (synCsn (.cv x)) B))
  have p0010 := @gOpeliunxp x A B (.cv y)
  have p0011 :=
    @gSyl6bb (.classEq C (synCop (.cv x) (.cv y)))
      (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (.classMem (synCop (.cv x) (.cv y)) (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0009 p0010
  have p0012 :=
    @gPm532i (.classEq C (synCop (.cv x) (.cv y)))
      (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0011
  have p0013 :=
    @gExbii
      (synWa (.classEq C (synCop (.cv x) (.cv y)))
        (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))))
      (synWa (.classEq C (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      y p0012
  have p0014 :=
    @gBitr3i
      (synWa (synWex y (.classEq C (synCop (.cv x) (.cv y))))
        (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))))
      (synWex y (synWa (.classEq C (synCop (.cv x) (.cv y)))
          (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))))
      (synWex y (synWa (.classEq C (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))))
      p0008 p0013
  have p0015 :=
    @gExbii
      (synWa (synWex y (.classEq C (synCop (.cv x) (.cv y))))
        (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))))
      (synWex y (synWa (.classEq C (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))))
      x p0014
  have p0016 :=
    @gN3bitr2i (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (synWa (synWex x (synWex y (.classEq C (synCop (.cv x) (.cv y)))))
        (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B))))
      (synWex x (synWa (synWex y (.classEq C (synCop (.cv x) (.cv y))))
          (.classMem C (synCiun x A (synCxp (synCsn (.cv x)) B)))))
      (synWex x (synWex y (synWa (.classEq C (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      p0004 p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_raliunxp`. -/
@[expose]
noncomputable def gRaliunxp (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (_dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_raliunxp_1 :
      Nominal.NPrf (.imp (.classEq (.cv x) (synCop (.cv y) (.cv z))) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWral x (synCiun y A (synCxp (synCsn (.cv y)) B)) ph)
        (synWral y A (synWral z B ps))) :=
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
  have dv_cache_0008 : x ∉ ((synCop (.cv y) (.cv z))).fv :=
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
    x ∉ ((Wff.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)).fv :=
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
    @gEliunxp y z A B (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @gImbi1i (.classMem (.cv x) (synCiun y A (synCxp (synCsn (.cv y)) B)))
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
            (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)))))
      ph p0000
  have p0002 :=
    @gN1923vv
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
        (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)))
      ph y z dv_cache_0006 dv_cache_0007
  have p0003 :=
    @gBitr4i (.imp (.classMem (.cv x) (synCiun y A (synCxp (synCsn (.cv y)) B))) ph)
      (.imp (synWex y (synWex z (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
              (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))))) ph)
      (.all y (.all z (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
              (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))
      p0001 p0002
  have p0004 :=
    @gAlbii (.imp (.classMem (.cv x) (synCiun y A (synCxp (synCsn (.cv y)) B))) ph)
      (.all y (.all z (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
              (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))
      x p0003
  have p0005 :=
    @gAlrot3
      (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
          (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)
      x y z
  have p0006 :=
    @gImpexp (.classEq (.cv x) (synCop (.cv y) (.cv z)))
      (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph
  have p0007 :=
    @gAlbii
      (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
          (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)
      (.imp (.classEq (.cv x) (synCop (.cv y) (.cv z)))
        (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph))
      x p0006
  have p0008 := @gVex y
  have p0009 := @gVex z
  have p0010 := @gOpex (.cv y) (.cv z) p0008 p0009
  have p0011 :=
    @gImbi2d (.classEq (.cv x) (synCop (.cv y) (.cv z))) ph ps
      (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) hyp_raliunxp_1
  have p0012 :=
    @gCeqsalv (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph)
      (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) x
      (synCop (.cv y) (.cv z)) dv_cache_0008 dv_cache_0009 p0010 p0011
  have p0013 :=
    @gBitri
      (.all x (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
            (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))
      (.all x (.imp (.classEq (.cv x) (synCop (.cv y) (.cv z)))
          (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph)))
      (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) p0007 p0012
  have p0014 :=
    @gN2albii
      (.all x (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
            (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))
      (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) y z p0013
  have p0015 :=
    @gBitri
      (.all x (.all y (.all z (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
                (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))))
      (.all y (.all z (.all x (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
                (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))))
      (.all y (.all z (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)))
      p0005 p0014
  have p0016 :=
    @gBitri
      (.all x (.imp (.classMem (.cv x) (synCiun y A (synCxp (synCsn (.cv y)) B))) ph))
      (.all x (.all y (.all z (.imp (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
                (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))))
      (.all y (.all z (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)))
      p0004 p0015
  have p0017 :=
    (Nominal.biimpRefl (synWral x (synCiun y A (synCxp (synCsn (.cv y)) B)) ph))
  have p0018 := @gR2al ps y z A B dv_cache_0001 dv_cache_0005
  have p0019 :=
    @gN3bitr4i
      (.all x (.imp (.classMem (.cv x) (synCiun y A (synCxp (synCsn (.cv y)) B))) ph))
      (.all y (.all z (.imp (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)))
      (synWral x (synCiun y A (synCxp (synCsn (.cv y)) B)) ph)
      (synWral y A (synWral z B ps)) p0016 p0017 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_rexiunxp`. -/
@[expose]
noncomputable def gRexiunxp (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_raliunxp_1 :
      Nominal.NPrf (.imp (.classEq (.cv x) (synCop (.cv y) (.cv z))) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWrex x (synCiun y A (synCxp (synCsn (.cv y)) B)) ph)
        (synWrex y A (synWrex z B ps))) :=
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
    @gNotbid (.classEq (.cv x) (synCop (.cv y) (.cv z))) ph ps hyp_raliunxp_1
  have p0001 :=
    @gRaliunxp (.neg ph) (.neg ps) x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0000
  have p0002 := @gRalnex ps z B
  have p0003 := @gRalbii (synWral z B (.neg ps)) (.neg (synWrex z B ps)) y A p0002
  have p0004 :=
    @gBitri (synWral x (synCiun y A (synCxp (synCsn (.cv y)) B)) (.neg ph))
      (synWral y A (synWral z B (.neg ps))) (synWral y A (.neg (synWrex z B ps)))
      p0001 p0003
  have p0005 :=
    @gNotbii (synWral x (synCiun y A (synCxp (synCsn (.cv y)) B)) (.neg ph))
      (synWral y A (.neg (synWrex z B ps))) p0004
  have p0006 := @gDfrex2 ph x (synCiun y A (synCxp (synCsn (.cv y)) B))
  have p0007 := @gDfrex2 (synWrex z B ps) y A
  have p0008 :=
    @gN3bitr4i
      (.neg (synWral x (synCiun y A (synCxp (synCsn (.cv y)) B)) (.neg ph)))
      (.neg (synWral y A (.neg (synWrex z B ps))))
      (synWrex x (synCiun y A (synCxp (synCsn (.cv y)) B)) ph)
      (synWrex y A (synWrex z B ps)) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_rexxp`. -/
@[expose]
noncomputable def gRexxp (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_raliunxp_1 :
      Nominal.NPrf (.imp (.classEq (.cv x) (synCop (.cv y) (.cv z))) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWrex x (synCxp A B) ph) (synWrex y A (synWrex z B ps))) :=
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
  have dv_cache_0003 : x ∉ ((synCiun y A (synCxp (synCsn (.cv y)) B))).fv :=
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
  have dv_cache_0004 : x ∉ ((synCxp A B)).fv :=
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
  have p0000 := @gIunxpconst y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gRexeqi ph x (synCiun y A (synCxp (synCsn (.cv y)) B)) (synCxp A B)
      dv_cache_0003 dv_cache_0004 p0000
  have p0002 :=
    @gRexiunxp ph ps x y z A B dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 hyp_raliunxp_1
  have p0003 :=
    @gBitr3i (synWrex x (synCxp A B) ph)
      (synWrex x (synCiun y A (synCxp (synCsn (.cv y)) B)) ph)
      (synWrex y A (synWrex z B ps)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_brel`. -/
@[expose]
noncomputable def gBrel (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_brelg_1 : Nominal.NPrf (synWss R (synCxp C D))) :
    Nominal.NPrf (.imp (synWbr A R B) (synWa (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := @gSsbri R (synCxp C D) A B hyp_brelg_1
  have p0001 := @gBrxp A B C D
  have p0002 :=
    @gSylib (synWbr A R B) (synWbr A (synCxp C D) B)
      (synWa (.classMem A C) (.classMem B D)) p0000 p0001
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

/-- Checked nominal proof certificate identified upstream as `g_xpundi`. -/
@[expose]
noncomputable def gXpundi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCxp A (synCun B C)) (synCun (synCxp A B) (synCxp A C))) :=
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
  have dv_cache_0003 : x ∉ ((synCun B C)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCun B C)).fv :=
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
  have p0000 := @gElun (.cv y) B C
  have p0001 :=
    @gAnbi2i (.classMem (.cv y) (synCun B C))
      (synWo (.classMem (.cv y) B) (.classMem (.cv y) C)) (.classMem (.cv x) A) p0000
  have p0002 := @gAndi (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv y) C)
  have p0003 :=
    @gBitri (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCun B C)))
      (synWa (.classMem (.cv x) A) (synWo (.classMem (.cv y) B) (.classMem (.cv y) C)))
      (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      p0001 p0002
  have p0004 :=
    @gOpabbii (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCun B C)))
      (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      x y p0003
  have p0005 :=
    @gUnopab (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)) x y
  have p0006 :=
    @gEqtr4i
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCun B C))))
      (synCopab x y (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))))
      (synCun (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))))
      p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A
      (synCun B C) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0005
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A C
      dv_cache_0001 dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0005
  have p0010 :=
    @gUneq12i (synCxp A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) (synCxp A C)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))) p0008 p0009
  have p0011 :=
    @gN3eqtr4i
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCun B C))))
      (synCun (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))))
      (synCxp A (synCun B C)) (synCun (synCxp A B) (synCxp A C)) p0006 p0007 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_xpundir`. -/
@[expose]
noncomputable def gXpundir (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.classEq (synCxp (synCun A B) C) (synCun (synCxp A C) (synCxp B C))) :=
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
  have dv_cache_0001 : x ∉ ((synCun A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCun A B)).fv :=
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
  have p0000 := @gElun (.cv x) A B
  have p0001 :=
    @gAnbi1i (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv y) C) p0000
  have p0002 := @gAndir (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv y) C)
  have p0003 :=
    @gBitri (synWa (.classMem (.cv x) (synCun A B)) (.classMem (.cv y) C))
      (synWa (synWo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv y) C))
      (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      p0001 p0002
  have p0004 :=
    @gOpabbii (synWa (.classMem (.cv x) (synCun A B)) (.classMem (.cv y) C))
      (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      x y p0003
  have p0005 :=
    @gUnopab (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y
  have p0006 :=
    @gEqtr4i
      (synCopab x y (synWa (.classMem (.cv x) (synCun A B)) (.classMem (.cv y) C)))
      (synCopab x y (synWo (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))
          (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      (synCun (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)))
        (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y (synCun A B)
      C dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A C
      dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y B C
      dv_cache_0008 dv_cache_0009 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0010 :=
    @gUneq12i (synCxp A C)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))) (synCxp B C)
      (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))) p0008 p0009
  have p0011 :=
    @gN3eqtr4i
      (synCopab x y (synWa (.classMem (.cv x) (synCun A B)) (.classMem (.cv y) C)))
      (synCun (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)))
        (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))))
      (synCxp (synCun A B) C) (synCun (synCxp A C) (synCxp B C)) p0006 p0007 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_brinxp2`. -/
@[expose]
noncomputable def gBrinxp2 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCin R (synCxp C D)) B)
        (synW3a (.classMem A C) (.classMem B D) (synWbr A R B))) :=
  by
  have p0000 := @gAncom (synWbr A R B) (synWbr A (synCxp C D) B)
  have p0001 := @gBrxp A B C D
  have p0002 :=
    @gAnbi1i (synWbr A (synCxp C D) B) (synWa (.classMem A C) (.classMem B D))
      (synWbr A R B) p0001
  have p0003 :=
    @gBitri (synWa (synWbr A R B) (synWbr A (synCxp C D) B))
      (synWa (synWbr A (synCxp C D) B) (synWbr A R B))
      (synWa (synWa (.classMem A C) (.classMem B D)) (synWbr A R B)) p0000 p0002
  have p0004 := @gBrin A B R (synCxp C D)
  have p0005 :=
    (Nominal.biimpRefl (synW3a (.classMem A C) (.classMem B D) (synWbr A R B)))
  have p0006 :=
    @gN3bitr4i (synWa (synWbr A R B) (synWbr A (synCxp C D) B))
      (synWa (synWa (.classMem A C) (.classMem B D)) (synWbr A R B))
      (synWbr A (synCin R (synCxp C D)) B)
      (synW3a (.classMem A C) (.classMem B D) (synWbr A R B)) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_brinxp`. -/
@[expose]
noncomputable def gBrinxp (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D))
        (synWb (synWbr A R B) (synWbr A (synCin R (synCxp C D)) B))) :=
  by
  have p0000 := @gBrinxp2 A B C D R
  have p0001 :=
    (Nominal.biimpRefl (synW3a (.classMem A C) (.classMem B D) (synWbr A R B)))
  have p0002 :=
    @gBitri (synWbr A (synCin R (synCxp C D)) B)
      (synW3a (.classMem A C) (.classMem B D) (synWbr A R B))
      (synWa (synWa (.classMem A C) (.classMem B D)) (synWbr A R B)) p0000 p0001
  have p0003 :=
    @gBaibr (synWbr A (synCin R (synCxp C D)) B)
      (synWa (.classMem A C) (.classMem B D)) (synWbr A R B) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_xp0r`. -/
@[expose]
noncomputable def gXp0r (A : Class) :
    Nominal.NPrf (.classEq (synCxp (synC0) A) (synC0)) :=
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
  have dv_cache_0008 : z ∉ ((synCxp (synC0) A)).fv :=
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
  have dv_cache_0009 : z ∉ ((synC0)).fv :=
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
    @gElxp x y (.cv z) (synC0) A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @gNoel (.cv x)
  have p0002 :=
    @gSimprl (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.classMem (.cv x) (synC0))
      (.classMem (.cv y) A)
  have p0003 :=
    @gMto
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synC0)) (.classMem (.cv y) A)))
      (.classMem (.cv x) (synC0)) p0001 p0002
  have p0004 :=
    @gNex
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synC0)) (.classMem (.cv y) A)))
      y p0003
  have p0005 :=
    @gNex
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) (synC0)) (.classMem (.cv y) A))))
      x p0004
  have p0006 := @gNoel (.cv z)
  have p0007 :=
    @gN2false
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synC0)) (.classMem (.cv y) A)))))
      (.classMem (.cv z) (synC0)) p0005 p0006
  have p0008 :=
    @gBitri (.classMem (.cv z) (synCxp (synC0) A))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synC0)) (.classMem (.cv y) A)))))
      (.classMem (.cv z) (synC0)) p0000 p0007
  have p0009 := @gEqriv z (synCxp (synC0) A) (synC0) dv_cache_0008 dv_cache_0009 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_xpvv`. -/
@[expose]
noncomputable def gXpvv :
    Nominal.NPrf (.classEq (synCxp (synCvv) (synCvv)) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synCxp (synCvv) (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gEqv x (synCxp (synCvv) (synCvv)) dv_cache_0001
  have p0001 := @gOpeq (.cv x)
  have p0002 := @gVex x
  have p0003 := @gProj1ex (.cv x) p0002
  have p0004 := @gProj2ex (.cv x) p0002
  have p0005 := @gOpelxp (synCproj1 (.cv x)) (synCproj2 (.cv x)) (synCvv) (synCvv)
  have p0006 :=
    @gMpbir2an
      (.classMem (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
        (synCxp (synCvv) (synCvv)))
      (.classMem (synCproj1 (.cv x)) (synCvv))
      (.classMem (synCproj2 (.cv x)) (synCvv)) p0003 p0004 p0005
  have p0007 :=
    @gEqeltri (.cv x) (synCop (synCproj1 (.cv x)) (synCproj2 (.cv x)))
      (synCxp (synCvv) (synCvv)) p0001 p0006
  have p0008 :=
    @gMpgbir (.classEq (synCxp (synCvv) (synCvv)) (synCvv))
      (.classMem (.cv x) (synCxp (synCvv) (synCvv))) x p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_ssrel`. -/
@[expose]
noncomputable def gSsrel (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWss A B) (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
              (.classMem (synCop (.cv x) (.cv y)) B))))) :=
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
  have dv_cache_0001 : x ∉ ((synWss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWss A B)).fv :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv x) (synCproj1 (.cv z)))).fv :=
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
  have dv_cache_0004 : x ∉ ((synCproj1 (.cv z))).fv :=
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
      ((Wff.all y (.imp (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
            (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B)))).fv :=
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
  have dv_cache_0006 : y ∉ ((synCproj2 (.cv z))).fv :=
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
      ((Wff.imp (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A)
          (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B))).fv :=
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
      ((Wff.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
              (.classMem (synCop (.cv x) (.cv y)) B))))).fv :=
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
  have p0000 := @gSsel A B (synCop (.cv x) (.cv y))
  have p0001 :=
    @gAlrimivv (synWss A B)
      (.imp (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (synCop (.cv x) (.cv y)) B))
      x y dv_cache_0001 dv_cache_0002 p0000
  have p0002 := @gVex z
  have p0003 := @gProj1ex (.cv z) p0002
  have p0004 := @gOpeq1 (.cv x) (synCproj1 (.cv z)) (.cv y)
  have p0005 :=
    @gEleq1d (.classEq (.cv x) (synCproj1 (.cv z))) (synCop (.cv x) (.cv y))
      (synCop (synCproj1 (.cv z)) (.cv y)) A p0004
  have p0006 :=
    @gEleq1d (.classEq (.cv x) (synCproj1 (.cv z))) (synCop (.cv x) (.cv y))
      (synCop (synCproj1 (.cv z)) (.cv y)) B p0004
  have p0007 :=
    @gImbi12d (.classEq (.cv x) (synCproj1 (.cv z)))
      (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
      (.classMem (synCop (.cv x) (.cv y)) B)
      (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B) p0005 p0006
  have p0008 :=
    @gAlbidv (.classEq (.cv x) (synCproj1 (.cv z)))
      (.imp (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (synCop (.cv x) (.cv y)) B))
      (.imp (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
        (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B))
      y dv_cache_0003 p0007
  have p0009 :=
    @gSpcv
      (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) B)))
      (.all y (.imp (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
          (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B)))
      x (synCproj1 (.cv z)) dv_cache_0004 dv_cache_0005 p0003 p0008
  have p0010 := @gProj2ex (.cv z) p0002
  have p0011 := @gOpeq2 (.cv y) (synCproj2 (.cv z)) (synCproj1 (.cv z))
  have p0012 :=
    @gEleq1d (.classEq (.cv y) (synCproj2 (.cv z)))
      (synCop (synCproj1 (.cv z)) (.cv y))
      (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A p0011
  have p0013 :=
    @gEleq1d (.classEq (.cv y) (synCproj2 (.cv z)))
      (synCop (synCproj1 (.cv z)) (.cv y))
      (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B p0011
  have p0014 :=
    @gImbi12d (.classEq (.cv y) (synCproj2 (.cv z)))
      (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
      (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A)
      (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B)
      (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B) p0012 p0013
  have p0015 :=
    @gSpcv
      (.imp (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
        (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B))
      (.imp (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A)
        (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B))
      y (synCproj2 (.cv z)) dv_cache_0006 dv_cache_0007 p0010 p0014
  have p0016 :=
    @gSyl
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      (.all y (.imp (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) A)
          (.classMem (synCop (synCproj1 (.cv z)) (.cv y)) B)))
      (.imp (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A)
        (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B))
      p0009 p0015
  have p0017 := @gOpeq (.cv z)
  have p0018 :=
    @gEleq1i (.cv z) (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A p0017
  have p0019 :=
    @gEleq1i (.cv z) (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B p0017
  have p0020 :=
    @gN3imtr4g
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) A)
      (.classMem (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z))) B)
      (.classMem (.cv z) A) (.classMem (.cv z) B) p0016 p0018 p0019
  have p0021 :=
    @gSsrdv
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      z A B dv_cache_0008 dv_cache_0009 dv_cache_0010 p0020
  have p0022 :=
    @gImpbii (synWss A B)
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      p0001 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_eqrel`. -/
@[expose]
noncomputable def gEqrel (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
              (.classMem (synCop (.cv x) (.cv y)) B))))) :=
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
    @gSsrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gSsrel x y B A dv_cache_0003 dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0002 :=
    @gAnbi12i (synWss A B)
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      (synWss B A)
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) B)
            (.classMem (synCop (.cv x) (.cv y)) A))))
      p0000 p0001
  have p0003 := @gEqss A B
  have p0004 :=
    @gN2albiim (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (.cv x) (.cv y)) B) x y
  have p0005 :=
    @gN3bitr4i (synWa (synWss A B) (synWss B A))
      (synWa (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
              (.classMem (synCop (.cv x) (.cv y)) B)))) (.all x (.all y
            (.imp (.classMem (synCop (.cv x) (.cv y)) B)
              (.classMem (synCop (.cv x) (.cv y)) A)))))
      (.classEq A B)
      (.all x (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ssopr`. -/
@[expose]
noncomputable def gSsopr (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (synWss A B) (.all x (.all y (.all z
              (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))) :=
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
      ((Wff.imp (.classMem (synCop (.cv w) (.cv z)) A)
          (.classMem (synCop (.cv w) (.cv z)) B))).fv :=
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
      ((Wff.imp (.classMem (synCop (.cv w) (.cv z)) A)
          (.classMem (synCop (.cv w) (.cv z)) B))).fv :=
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
  have dv_cache_0011 : w ∉ ((synCop (.cv x) (.cv y))).fv :=
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
      ((Wff.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
          (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))).fv :=
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
    @gSsrel w z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gAlcom
      (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B))
      w z
  have p0002 :=
    @gBitri (synWss A B)
      (.all w (.all z (.imp (.classMem (synCop (.cv w) (.cv z)) A)
            (.classMem (synCop (.cv w) (.cv z)) B))))
      (.all z (.all w (.imp (.classMem (synCop (.cv w) (.cv z)) A)
            (.classMem (synCop (.cv w) (.cv z)) B))))
      p0000 p0001
  have p0003 := @gVex w
  have p0004 := @gOpeqex x y (.cv w) (synCvv) dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gA1bi (synWex x (synWex y (.classEq (.cv w) (synCop (.cv x) (.cv y)))))
      (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B))
      p0005
  have p0007 :=
    @gN1923vv (.classEq (.cv w) (synCop (.cv x) (.cv y)))
      (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B))
      x y dv_cache_0009 dv_cache_0010
  have p0008 :=
    @gBitr4i
      (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B))
      (.imp (synWex x (synWex y (.classEq (.cv w) (synCop (.cv x) (.cv y)))))
        (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B)))
      (.all x (.all y (.imp (.classEq (.cv w) (synCop (.cv x) (.cv y)))
            (.imp (.classMem (synCop (.cv w) (.cv z)) A)
              (.classMem (synCop (.cv w) (.cv z)) B)))))
      p0006 p0007
  have p0009 :=
    @gAlbii
      (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B))
      (.all x (.all y (.imp (.classEq (.cv w) (synCop (.cv x) (.cv y)))
            (.imp (.classMem (synCop (.cv w) (.cv z)) A)
              (.classMem (synCop (.cv w) (.cv z)) B)))))
      w p0008
  have p0010 :=
    @gAlrot3
      (.imp (.classEq (.cv w) (synCop (.cv x) (.cv y)))
        (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B)))
      w x y
  have p0011 := @gVex x
  have p0012 := @gVex y
  have p0013 := @gOpex (.cv x) (.cv y) p0011 p0012
  have p0014 := @gOpeq1 (.cv w) (synCop (.cv x) (.cv y)) (.cv z)
  have p0015 :=
    @gEleq1d (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synCop (.cv w) (.cv z))
      (synCop (synCop (.cv x) (.cv y)) (.cv z)) A p0014
  have p0016 :=
    @gEleq1d (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synCop (.cv w) (.cv z))
      (synCop (synCop (.cv x) (.cv y)) (.cv z)) B p0014
  have p0017 :=
    @gImbi12d (.classEq (.cv w) (synCop (.cv x) (.cv y)))
      (.classMem (synCop (.cv w) (.cv z)) A)
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
      (.classMem (synCop (.cv w) (.cv z)) B)
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B) p0015 p0016
  have p0018 :=
    @gCeqsalv
      (.imp (.classMem (synCop (.cv w) (.cv z)) A) (.classMem (synCop (.cv w) (.cv z)) B))
      (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))
      w (synCop (.cv x) (.cv y)) dv_cache_0011 dv_cache_0012 p0013 p0017
  have p0019 :=
    @gN2albii
      (.all w (.imp (.classEq (.cv w) (synCop (.cv x) (.cv y)))
          (.imp (.classMem (synCop (.cv w) (.cv z)) A)
            (.classMem (synCop (.cv w) (.cv z)) B))))
      (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))
      x y p0018
  have p0020 :=
    @gN3bitri
      (.all w (.imp (.classMem (synCop (.cv w) (.cv z)) A)
          (.classMem (synCop (.cv w) (.cv z)) B)))
      (.all w (.all x (.all y (.imp (.classEq (.cv w) (synCop (.cv x) (.cv y)))
              (.imp (.classMem (synCop (.cv w) (.cv z)) A)
                (.classMem (synCop (.cv w) (.cv z)) B))))))
      (.all x (.all y (.all w (.imp (.classEq (.cv w) (synCop (.cv x) (.cv y)))
              (.imp (.classMem (synCop (.cv w) (.cv z)) A)
                (.classMem (synCop (.cv w) (.cv z)) B))))))
      (.all x (.all y (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))
      p0009 p0010 p0019
  have p0021 :=
    @gAlbii
      (.all w (.imp (.classMem (synCop (.cv w) (.cv z)) A)
          (.classMem (synCop (.cv w) (.cv z)) B)))
      (.all x (.all y (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))
      z p0020
  have p0022 :=
    @gAlrot3
      (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))
      z x y
  have p0023 :=
    @gN3bitri (synWss A B)
      (.all z (.all w (.imp (.classMem (synCop (.cv w) (.cv z)) A)
            (.classMem (synCop (.cv w) (.cv z)) B))))
      (.all z (.all x (.all y (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))
      (.all x (.all y (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))
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

/-- Checked nominal proof certificate identified upstream as `g_eqopr`. -/
@[expose]
noncomputable def gEqopr (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (.all y (.all z
              (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))) :=
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
    @gSsopr x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @gSsopr x y z B A dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @gAnbi12i (synWss A B)
      (.all x (.all y (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))
      (synWss B A)
      (.all x (.all y (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)))))
      p0000 p0001
  have p0003 := @gEqss A B
  have p0004 :=
    @gN2albiim (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B) y z
  have p0005 :=
    @gAlbii
      (.all y (.all z (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))
      (synWa (.all y (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))) (.all y (.all z
            (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)))))
      x p0004
  have p0006 :=
    @gN1926
      (.all y (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))
      (.all y (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)
            (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))))
      x
  have p0007 :=
    @gBitri
      (.all x (.all y (.all z (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))
      (.all x (synWa (.all y (.all z
              (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))) (.all y (.all z
              (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))))))
      (synWa (.all x (.all y (.all z
              (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))) (.all x (.all y
            (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))))))
      p0005 p0006
  have p0008 :=
    @gN3bitr4i (synWa (synWss A B) (synWss B A))
      (synWa (.all x (.all y (.all z
              (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))) (.all x (.all y
            (.all z (.imp (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)
                (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))))))
      (.classEq A B)
      (.all x (.all y (.all z (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
              (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B)))))
      p0002 p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_relssi`. -/
@[expose]
noncomputable def gRelssi (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_relssi_1 : Nominal.NPrf (.imp (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) B))) :
    Nominal.NPrf (synWss A B) :=
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
    @gSsrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := Nominal.gen hyp_relssi_1 y
  have p0002 :=
    @gMpgbir (synWss A B)
      (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) B)))
      x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_relssdv`. -/
@[expose]
noncomputable def gRelssdv (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_relssdv_1 : Nominal.NPrf (.imp ph (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B)))) :
    Nominal.NPrf (.imp ph (synWss A B)) :=
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
    @gAlrimivv ph
      (.imp (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (synCop (.cv x) (.cv y)) B))
      x y dv_cache_0001 dv_cache_0002 hyp_relssdv_1
  have p0001 :=
    @gSsrel x y A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @gSylibr ph
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      (synWss A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqrelriv`. -/
@[expose]
noncomputable def gEqrelriv (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_eqrelriv_1 : Nominal.NPrf (synWb (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) B))) :
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
    @gEqrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := Nominal.gen hyp_eqrelriv_1 y
  have p0002 :=
    @gMpgbir (.classEq A B)
      (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) B)))
      x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqbrriv`. -/
@[expose]
noncomputable def gEqbrriv (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_eqbrriv_1 :
      Nominal.NPrf (synWb (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y)))) :
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
  have p0000 := (Nominal.biimpRefl (synWbr (.cv x) A (.cv y)))
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) B (.cv y)))
  have p0002 :=
    @gN3bitr3i (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (synCop (.cv x) (.cv y)) B)
      hyp_eqbrriv_1 p0000 p0001
  have p0003 :=
    @gEqrelriv x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eqrelrdv`. -/
@[expose]
noncomputable def gEqrelrdv (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_eqrelrdv_1 : Nominal.NPrf (.imp ph (synWb (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B)))) :
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
    @gAlrimivv ph
      (synWb (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (synCop (.cv x) (.cv y)) B))
      x y dv_cache_0001 dv_cache_0002 hyp_eqrelrdv_1
  have p0001 :=
    @gEqrel x y A B dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @gSylibr ph
      (.all x (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) B))))
      (.classEq A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqoprriv`. -/
@[expose]
noncomputable def gEqoprriv (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_eqoprriv_1 : Nominal.NPrf
        (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
          (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))) :
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
    @gEqopr x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @gGen2
      (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
        (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))
      y z hyp_eqoprriv_1
  have p0002 :=
    @gMpgbir (.classEq A B)
      (.all y (.all z (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
            (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) B))))
      x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_xpss12`. -/
@[expose]
noncomputable def gXpss12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (synWss A B) (synWss C D)) (synWss (synCxp A C) (synCxp B D))) :=
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
  have dv_cache_0001 : x ∉ ((synWa (synWss A B) (synWss C D))).fv := by
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
  have dv_cache_0002 : y ∉ ((synWa (synWss A B) (synWss C D))).fv :=
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
  have p0000 := @gSsel A B (.cv x)
  have p0001 := @gSsel C D (.cv y)
  have p0002 :=
    @gIm2anan9 (synWss A B) (.classMem (.cv x) A) (.classMem (.cv x) B) (synWss C D)
      (.classMem (.cv y) C) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @gSsopab2dv (synWa (synWss A B) (synWss C D))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) C))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) D)) x y dv_cache_0001 dv_cache_0002
      p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y B D
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0007
  have p0006 :=
    @gN3sstr4g (synWa (synWss A B) (synWss C D))
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) C)))
      (synCopab x y (synWa (.classMem (.cv x) B) (.classMem (.cv y) D))) (synCxp A C)
      (synCxp B D) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_xpss1`. -/
@[expose]
noncomputable def gXpss1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCxp A C) (synCxp B C))) :=
  by
  have p0000 := @gSsid C
  have p0001 := @gXpss12 A B C C
  have p0002 :=
    @gMpan2 (synWss A B) (synWss C C) (synWss (synCxp A C) (synCxp B C)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_xpss2`. -/
@[expose]
noncomputable def gXpss2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCxp C A) (synCxp C B))) :=
  by
  have p0000 := @gSsid C
  have p0001 := @gXpss12 C C A B
  have p0002 :=
    @gMpan (synWss C C) (synWss A B) (synWss (synCxp C A) (synCxp C B)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_br1st`. -/
@[expose]
noncomputable def gBr1st (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_br1st_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr A (synC1st) B) (synWex x (.classEq A (synCop B (.cv x))))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem A (synCvv))).fv := by
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
  have dv_cache_0011 : y ∉ ((synWex x (.classEq A (synCop B (.cv x))))).fv :=
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
  have dv_cache_0012 : z ∉ ((synWex x (.classEq A (synCop B (.cv x))))).fv :=
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
  have p0000 := @gBrex A B (synC1st)
  have p0001 :=
    @gSimpld (synWbr A (synC1st) B) (.classMem A (synCvv)) (.classMem B (synCvv))
      p0000
  have p0002 := @gVex x
  have p0003 := @gOpex B (.cv x) hyp_br1st_1 p0002
  have p0004 := @gEleq1 A (synCop B (.cv x)) (synCvv)
  have p0005 :=
    @gMpbiri (.classEq A (synCop B (.cv x))) (.classMem A (synCvv))
      (.classMem (synCop B (.cv x)) (synCvv)) p0003 p0004
  have p0006 :=
    @gExlimiv (.classEq A (synCop B (.cv x))) (.classMem A (synCvv)) x dv_cache_0001
      p0005
  have p0007 := @gEqeq1 (.cv y) A (synCop (.cv z) (.cv x))
  have p0008 :=
    @gExbidv (.classEq (.cv y) A) (.classEq (.cv y) (synCop (.cv z) (.cv x)))
      (.classEq A (synCop (.cv z) (.cv x))) x dv_cache_0002 p0007
  have p0009 := @gOpeq1 (.cv z) B (.cv x)
  have p0010 :=
    @gEqeq2d (.classEq (.cv z) B) (synCop (.cv z) (.cv x)) (synCop B (.cv x)) A p0009
  have p0011 :=
    @gExbidv (.classEq (.cv z) B) (.classEq A (synCop (.cv z) (.cv x)))
      (.classEq A (synCop B (.cv x))) x dv_cache_0003 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDf1st y z x
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @gBrabg (synWex x (.classEq (.cv y) (synCop (.cv z) (.cv x))))
      (synWex x (.classEq A (synCop (.cv z) (.cv x))))
      (synWex x (.classEq A (synCop B (.cv x)))) y z A B (synCvv) (synCvv) (synC1st)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0004 p0008 p0011 p0012
  have p0014 :=
    @gMpan2 (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr A (synC1st) B) (synWex x (.classEq A (synCop B (.cv x)))))
      hyp_br1st_1 p0013
  have p0015 :=
    @gPm521nii (synWbr A (synC1st) B) (.classMem A (synCvv))
      (synWex x (.classEq A (synCop B (.cv x)))) p0001 p0006 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_br2nd`. -/
@[expose]
noncomputable def gBr2nd (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_br1st_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr A (synC2nd) B) (synWex x (.classEq A (synCop (.cv x) B)))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem A (synCvv))).fv := by
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
  have dv_cache_0011 : y ∉ ((synWex x (.classEq A (synCop (.cv x) B)))).fv :=
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
  have dv_cache_0012 : z ∉ ((synWex x (.classEq A (synCop (.cv x) B)))).fv :=
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
  have p0000 := @gBrex A B (synC2nd)
  have p0001 :=
    @gSimpld (synWbr A (synC2nd) B) (.classMem A (synCvv)) (.classMem B (synCvv))
      p0000
  have p0002 := @gVex x
  have p0003 := @gOpex (.cv x) B p0002 hyp_br1st_1
  have p0004 := @gEleq1 A (synCop (.cv x) B) (synCvv)
  have p0005 :=
    @gMpbiri (.classEq A (synCop (.cv x) B)) (.classMem A (synCvv))
      (.classMem (synCop (.cv x) B) (synCvv)) p0003 p0004
  have p0006 :=
    @gExlimiv (.classEq A (synCop (.cv x) B)) (.classMem A (synCvv)) x dv_cache_0001
      p0005
  have p0007 := @gEqeq1 (.cv y) A (synCop (.cv x) (.cv z))
  have p0008 :=
    @gExbidv (.classEq (.cv y) A) (.classEq (.cv y) (synCop (.cv x) (.cv z)))
      (.classEq A (synCop (.cv x) (.cv z))) x dv_cache_0002 p0007
  have p0009 := @gOpeq2 (.cv z) B (.cv x)
  have p0010 :=
    @gEqeq2d (.classEq (.cv z) B) (synCop (.cv x) (.cv z)) (synCop (.cv x) B) A p0009
  have p0011 :=
    @gExbidv (.classEq (.cv z) B) (.classEq A (synCop (.cv x) (.cv z)))
      (.classEq A (synCop (.cv x) B)) x dv_cache_0003 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDf2nd y z x
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @gBrabg (synWex x (.classEq (.cv y) (synCop (.cv x) (.cv z))))
      (synWex x (.classEq A (synCop (.cv x) (.cv z))))
      (synWex x (.classEq A (synCop (.cv x) B))) y z A B (synCvv) (synCvv) (synC2nd)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0004 p0008 p0011 p0012
  have p0014 :=
    @gMpan2 (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr A (synC2nd) B) (synWex x (.classEq A (synCop (.cv x) B))))
      hyp_br1st_1 p0013
  have p0015 :=
    @gPm521nii (synWbr A (synC2nd) B) (.classMem A (synCvv))
      (synWex x (.classEq A (synCop (.cv x) B))) p0001 p0006 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
