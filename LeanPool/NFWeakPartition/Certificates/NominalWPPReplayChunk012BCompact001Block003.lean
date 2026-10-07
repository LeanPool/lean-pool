/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012BCompact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_n_1st2nd2`. -/
@[expose]
noncomputable def gN1st2nd2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCxp B C))
        (.classEq A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A)))) :=
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
  have dv_cache_0008 :
    y ∉ ((Wff.classEq A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    x ∉ ((Wff.classEq A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gElxp2 x y A B C dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gOpfv1st (.cv x) (.cv y) p0001 p0002
  have p0004 := @gOpfv2nd (.cv x) (.cv y) p0001 p0002
  have p0005 :=
    @gOpeq12i (synCfv (synC1st) (synCop (.cv x) (.cv y))) (.cv x)
      (synCfv (synC2nd) (synCop (.cv x) (.cv y))) (.cv y) p0003 p0004
  have p0006 :=
    @gEqcomi
      (synCop (synCfv (synC1st) (synCop (.cv x) (.cv y)))
        (synCfv (synC2nd) (synCop (.cv x) (.cv y))))
      (synCop (.cv x) (.cv y)) p0005
  have p0007 := @gId (.classEq A (synCop (.cv x) (.cv y)))
  have p0008 := @gFveq2 A (synCop (.cv x) (.cv y)) (synC1st)
  have p0009 := @gFveq2 A (synCop (.cv x) (.cv y)) (synC2nd)
  have p0010 :=
    @gOpeq12d (.classEq A (synCop (.cv x) (.cv y))) (synCfv (synC1st) A)
      (synCfv (synC1st) (synCop (.cv x) (.cv y))) (synCfv (synC2nd) A)
      (synCfv (synC2nd) (synCop (.cv x) (.cv y))) p0008 p0009
  have p0011 :=
    @gN3eqtr4a (.classEq A (synCop (.cv x) (.cv y))) (synCop (.cv x) (.cv y))
      (synCop (synCfv (synC1st) (synCop (.cv x) (.cv y)))
        (synCfv (synC2nd) (synCop (.cv x) (.cv y))))
      A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A)) p0006 p0007 p0010
  have p0012 :=
    @gRexlimivw (.classEq A (synCop (.cv x) (.cv y)))
      (.classEq A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A))) y C
      dv_cache_0008 p0011
  have p0013 :=
    @gRexlimivw (synWrex y C (.classEq A (synCop (.cv x) (.cv y))))
      (.classEq A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A))) x B
      dv_cache_0009 p0012
  have p0014 :=
    @gSylbi (.classMem A (synCxp B C))
      (synWrex x B (synWrex y C (.classEq A (synCop (.cv x) (.cv y)))))
      (.classEq A (synCop (synCfv (synC1st) A) (synCfv (synC2nd) A))) p0000 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_fununiq`. -/
@[expose]
noncomputable def gFununiq (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWfun F) (synWbr A F B) (synWbr A F C)) (.classEq B C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_x_not_F : x ∉ F.fv := by
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
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
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
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0003 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
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
  have dv_cache_0009 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0010 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0011 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0012 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0013 : x ∉ (C).fv :=
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
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0014 : y ∉ (C).fv :=
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
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0015 : z ∉ (C).fv :=
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
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0016 :
    x ∉ ((Wff.imp (synWa (synWbr A F B) (synWbr A F C)) (.classEq B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, fresh_x_not_A,
          fresh_x_not_B, fresh_x_not_F, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0017 :
    y ∉ ((Wff.imp (synWa (synWbr A F B) (synWbr A F C)) (.classEq B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, fresh_y_not_A,
          fresh_y_not_B, fresh_y_not_F, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0018 :
    z ∉ ((Wff.imp (synWa (synWbr A F B) (synWbr A F C)) (.classEq B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, fresh_z_not_A,
          fresh_z_not_B, fresh_z_not_F, fresh_z_not_C, or_false, not_false_eq_true])
  have p0000 := @gBrex A B F
  have p0001 := @gBrex A C F
  have p0002 :=
    @gAnim12i (synWbr A F B) (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWbr A F C) (synWa (.classMem A (synCvv)) (.classMem C (synCvv))) p0000 p0001
  have p0003 :=
    @gAnandi (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0004 :=
    @gSylibr (synWa (synWbr A F B) (synWbr A F C))
      (synWa (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (synWa (.classMem A (synCvv)) (.classMem C (synCvv))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0002 p0003
  have p0005 :=
    @gN3adant1 (synWbr A F B) (synWbr A F C)
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      (synWfun F) p0004
  have p0006 :=
    @gDffun2 x y z F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0007 := @gBreq12 (.cv x) A (.cv y) B F
  have p0008 :=
    @gN3adant3 (.classEq (.cv x) A) (.classEq (.cv y) B)
      (synWb (synWbr (.cv x) F (.cv y)) (synWbr A F B)) (.classEq (.cv z) C) p0007
  have p0009 := @gBreq12 (.cv x) A (.cv z) C F
  have p0010 :=
    @gN3adant2 (.classEq (.cv x) A) (.classEq (.cv z) C)
      (synWb (synWbr (.cv x) F (.cv z)) (synWbr A F C)) (.classEq (.cv y) B) p0009
  have p0011 :=
    @gAnbi12d (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      (synWbr (.cv x) F (.cv y)) (synWbr A F B) (synWbr (.cv x) F (.cv z))
      (synWbr A F C) p0008 p0010
  have p0012 := @gEqeq12 (.cv y) B (.cv z) C
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (synWb (.objEq y z) (.classEq B C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
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
      p0012
  have p0013 :=
    @gN3adant1 (.classEq (.cv y) B) (.classEq (.cv z) C)
      (synWb (.objEq y z) (.classEq B C)) (.classEq (.cv x) A) p0013_e00_recanon
  have p0014 :=
    @gImbi12d (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
      (synWa (synWbr A F B) (synWbr A F C)) (.objEq y z) (.classEq B C) p0011 p0013
  have p0015 :=
    @gSpc3gv
      (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr A F B) (synWbr A F C)) (.classEq B C)) x y z A B C (synCvv)
      (synCvv) (synCvv) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0014
  have p0016 :=
    @gSyl5bi (synWfun F)
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
              (.objEq y z)))))
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (synWbr A F B) (synWbr A F C)) (.classEq B C)) p0006 p0015
  have p0017 :=
    @gExp4a
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWfun F) (synWbr A F B) (synWbr A F C) (.classEq B C) p0016
  have p0018 :=
    @gN3impd
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWfun F) (synWbr A F B) (synWbr A F C) (.classEq B C) p0017
  have p0019 :=
    @gN3expb (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
      (.imp (synW3a (synWfun F) (synWbr A F B) (synWbr A F C)) (.classEq B C)) p0018
  have p0020 :=
    @gMpcom
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      (synW3a (synWfun F) (synWbr A F B) (synWbr A F C)) (.classEq B C) p0005 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_cnvsi`. -/
@[expose]
noncomputable def gCnvsi (R : Class) :
    Nominal.NPrf (.classEq (synCcnv (synCsi R)) (synCsi (synCcnv R))) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
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
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (h)
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_b_ne_a : b ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have dv_cache_0001 : b ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0005 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0006 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0007 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0008 : a ∉ ((synCcnv R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_a_not_R,
          not_false_eq_true])
  have dv_cache_0009 : b ∉ ((synCcnv R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_b_not_R,
          not_false_eq_true])
  have dv_cache_0010 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : x ∉ ((synCcnv (synCsi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synCcnv (synCsi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0013 : x ∉ ((synCsi (synCcnv R))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0014 : y ∉ ((synCsi (synCcnv R))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0015 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @gN3ancoma (.classEq (.cv y) (synCsn (.cv b))) (.classEq (.cv x) (synCsn (.cv a)))
      (synWbr (.cv b) R (.cv a))
  have p0001 := @gBrcnv (.cv a) (.cv b) R
  have p0002 :=
    @gN3anbi3i (synWbr (.cv a) (synCcnv R) (.cv b)) (synWbr (.cv b) R (.cv a))
      (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))) p0001
  have p0003 :=
    @gBitr4i
      (synW3a (.classEq (.cv y) (synCsn (.cv b))) (.classEq (.cv x) (synCsn (.cv a)))
        (synWbr (.cv b) R (.cv a)))
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (synWbr (.cv b) R (.cv a)))
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (synWbr (.cv a) (synCcnv R) (.cv b)))
      p0000 p0002
  have p0004 :=
    @gN2exbii
      (synW3a (.classEq (.cv y) (synCsn (.cv b))) (.classEq (.cv x) (synCsn (.cv a)))
        (synWbr (.cv b) R (.cv a)))
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (synWbr (.cv a) (synCcnv R) (.cv b)))
      a b p0003
  have p0005 := @gBrcnv (.cv x) (.cv y) (synCsi R)
  have p0006 :=
    @gBrsi b a (.cv y) (.cv x) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @gExcom
      (synW3a (.classEq (.cv y) (synCsn (.cv b))) (.classEq (.cv x) (synCsn (.cv a)))
        (synWbr (.cv b) R (.cv a)))
      b a
  have p0008 :=
    @gN3bitri (synWbr (.cv x) (synCcnv (synCsi R)) (.cv y))
      (synWbr (.cv y) (synCsi R) (.cv x))
      (synWex b (synWex a (synW3a (.classEq (.cv y) (synCsn (.cv b)))
            (.classEq (.cv x) (synCsn (.cv a))) (synWbr (.cv b) R (.cv a)))))
      (synWex a (synWex b (synW3a (.classEq (.cv y) (synCsn (.cv b)))
            (.classEq (.cv x) (synCsn (.cv a))) (synWbr (.cv b) R (.cv a)))))
      p0005 p0006 p0007
  have p0009 :=
    @gBrsi a b (.cv x) (.cv y) (synCcnv R) dv_cache_0004 dv_cache_0003 dv_cache_0002
      dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0010 :=
    @gN3bitr4i
      (synWex a (synWex b (synW3a (.classEq (.cv y) (synCsn (.cv b)))
            (.classEq (.cv x) (synCsn (.cv a))) (synWbr (.cv b) R (.cv a)))))
      (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) (synCcnv R) (.cv b)))))
      (synWbr (.cv x) (synCcnv (synCsi R)) (.cv y))
      (synWbr (.cv x) (synCsi (synCcnv R)) (.cv y)) p0004 p0008 p0009
  have p0011 :=
    @gEqbrriv x y (synCcnv (synCsi R)) (synCsi (synCcnv R)) dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_dmsi`. -/
@[expose]
noncomputable def gDmsi (R : Class) :
    Nominal.NPrf (.classEq (synCdm (synCsi R)) (synCpw1 (synCdm R))) :=
  by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let b : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (h)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (synCsn (.cv a)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_a, or_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((Wff.classEq (.cv x) (synCsn (.cv a)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCsn (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_b,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synWbr (.cv a) R (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0005 : b ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_a, not_false_eq_true])
  have dv_cache_0006 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv :=
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
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synCsi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0009 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0013 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0014 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0015 : a ∉ ((synCdm R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_a_not_R,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((synCdm (synCsi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0017 : x ∉ ((synCpw1 (synCdm R))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_R,
          not_false_eq_true])
  have p0000 :=
    @gN3anass (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
      (synWbr (.cv a) R (.cv b))
  have p0001 :=
    @gN2exbii
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (synWbr (.cv a) R (.cv b)))
      (synWa (.classEq (.cv x) (synCsn (.cv a)))
        (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))
      y b p0000
  have p0002 :=
    @gN1942vv (.classEq (.cv x) (synCsn (.cv a)))
      (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))) y b
      dv_cache_0001 dv_cache_0002
  have p0003 :=
    @gBitri
      (synWex y (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      (synWex y (synWex b (synWa (.classEq (.cv x) (synCsn (.cv a)))
            (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (synWex y (synWex b
            (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      p0001 p0002
  have p0004 := @gSnex (.cv b)
  have p0005 := @gIsseti y (synCsn (.cv b)) dv_cache_0003 p0004
  have p0006 :=
    @gN1941v (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)) y
      dv_cache_0004
  have p0007 :=
    @gMpbiran
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))
      (synWex y (.classEq (.cv y) (synCsn (.cv b)))) (synWbr (.cv a) R (.cv b)) p0005
      p0006
  have p0008 :=
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))
      (synWbr (.cv a) R (.cv b)) b p0007
  have p0009 :=
    @gExcom (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))) y b
  have p0010 := @gEldm b (.cv a) R dv_cache_0005 dv_cache_0006
  have p0011 :=
    @gN3bitr4i
      (synWex b (synWex y
          (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      (synWex b (synWbr (.cv a) R (.cv b)))
      (synWex y (synWex b
          (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      (.classMem (.cv a) (synCdm R)) p0008 p0009 p0010
  have p0012 :=
    @gAnbi2i
      (synWex y (synWex b
          (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      (.classMem (.cv a) (synCdm R)) (.classEq (.cv x) (synCsn (.cv a))) p0011
  have p0013 :=
    @gAncom (.classEq (.cv x) (synCsn (.cv a))) (.classMem (.cv a) (synCdm R))
  have p0014 :=
    @gBitri
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (synWex y (synWex b
            (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classMem (.cv a) (synCdm R)))
      (synWa (.classMem (.cv a) (synCdm R)) (.classEq (.cv x) (synCsn (.cv a)))) p0012
      p0013
  have p0015 :=
    @gBitri
      (synWex y (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (synWex y (synWex b
            (synWa (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      (synWa (.classMem (.cv a) (synCdm R)) (.classEq (.cv x) (synCsn (.cv a)))) p0003
      p0014
  have p0016 :=
    @gExbii
      (synWex y (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      (synWa (.classMem (.cv a) (synCdm R)) (.classEq (.cv x) (synCsn (.cv a)))) a
      p0015
  have p0017 :=
    @gExcom
      (synWex b
        (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
          (synWbr (.cv a) R (.cv b))))
      y a
  have p0018 :=
    (Nominal.biimpRefl (synWrex a (synCdm R) (.classEq (.cv x) (synCsn (.cv a)))))
  have p0019 :=
    @gN3bitr4i
      (synWex a (synWex y (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      (synWex a (synWa (.classMem (.cv a) (synCdm R)) (.classEq (.cv x) (synCsn (.cv a)))))
      (synWex y (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      (synWrex a (synCdm R) (.classEq (.cv x) (synCsn (.cv a)))) p0016 p0017 p0018
  have p0020 := @gEldm y (.cv x) (synCsi R) dv_cache_0007 dv_cache_0008
  have p0021 :=
    @gBrsi a b (.cv x) (.cv y) R dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0006 dv_cache_0014
  have p0022 :=
    @gExbii (synWbr (.cv x) (synCsi R) (.cv y))
      (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b)))))
      y p0021
  have p0023 :=
    @gBitri (.classMem (.cv x) (synCdm (synCsi R)))
      (synWex y (synWbr (.cv x) (synCsi R) (.cv y)))
      (synWex y (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      p0020 p0022
  have p0024 := @gElpw1 a (.cv x) (synCdm R) dv_cache_0009 dv_cache_0015
  have p0025 :=
    @gN3bitr4i
      (synWex y (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) R (.cv b))))))
      (synWrex a (synCdm R) (.classEq (.cv x) (synCsn (.cv a))))
      (.classMem (.cv x) (synCdm (synCsi R))) (.classMem (.cv x) (synCpw1 (synCdm R)))
      p0019 p0023 p0024
  have p0026 :=
    @gEqriv x (synCdm (synCsi R)) (synCpw1 (synCdm R)) dv_cache_0016 dv_cache_0017
      p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_funsi`. -/
@[expose]
noncomputable def gFunsi (F : Class) :
    Nominal.NPrf (.imp (synWfun F) (synWfun (synCsi F))) :=
  by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (h)
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (h)
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (h)
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_c : z ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_z_ne_d : z ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_d_ne_z : d ≠ z := Ne.symm fresh_z_ne_d
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have dv_cache_0001 : a ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0005 : a ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_F, not_false_eq_true])
  have dv_cache_0006 : b ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_F, not_false_eq_true])
  have dv_cache_0007 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0008 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0010 : c ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_z, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_z, not_false_eq_true])
  have dv_cache_0012 : c ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_F, not_false_eq_true])
  have dv_cache_0013 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_F, not_false_eq_true])
  have dv_cache_0014 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0015 :
    d ∉
      ((synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
          (synWbr (.cv a) F (.cv b)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_b, fresh_d_not_F, fresh_d_ne_x,
          fresh_d_ne_y, or_false, not_false_eq_true])
  have dv_cache_0016 :
    c ∉
      ((synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
          (synWbr (.cv a) F (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_b, fresh_c_not_F, fresh_c_ne_x,
          fresh_c_ne_y, or_false, not_false_eq_true])
  have dv_cache_0017 :
    a ∉
      ((synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_d, fresh_a_not_F, fresh_a_ne_x,
          fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0018 :
    b ∉
      ((synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_d, fresh_b_not_F, fresh_b_ne_x,
          fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0019 : d ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0020 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0021 : c ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_z, or_false, not_false_eq_true])
  have dv_cache_0022 : d ∉ ((Wff.objEq y z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_z, or_false, not_false_eq_true])
  have dv_cache_0023 : c ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_c_not_F,
          not_false_eq_true])
  have dv_cache_0024 : d ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_d_not_F,
          not_false_eq_true])
  have dv_cache_0025 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0026 : b ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_a_not_F,
          not_false_eq_true])
  have dv_cache_0028 : b ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_b_not_F,
          not_false_eq_true])
  have dv_cache_0029 : z ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_z_not_F,
          not_false_eq_true])
  have dv_cache_0030 : x ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0031 : y ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_y_not_F,
          not_false_eq_true])
  have dv_cache_0032 : x ∉ ((synCsi F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0033 : y ∉ ((synCsi F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_y_not_F,
          not_false_eq_true])
  have dv_cache_0034 : z ∉ ((synCsi F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_z_not_F,
          not_false_eq_true])
  have dv_cache_0035 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0036 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0037 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @gBrsi a b (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gBrsi c d (.cv x) (.cv z) F dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0002 :=
    @gAnbi12i (synWbr (.cv x) (synCsi F) (.cv y))
      (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) F (.cv b)))))
      (synWbr (.cv x) (synCsi F) (.cv z))
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d)))))
      p0000 p0001
  have p0003 :=
    @gEe4anv
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (synWbr (.cv a) F (.cv b)))
      (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
        (synWbr (.cv c) F (.cv d)))
      a b c d dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020
  have p0004 :=
    @gBitr4i
      (synWa (synWbr (.cv x) (synCsi F) (.cv y)) (synWbr (.cv x) (synCsi F) (.cv z)))
      (synWa (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) F (.cv b))))) (synWex c
          (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
              (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))))))
      (synWex a (synWex b (synWex c (synWex d (synWa
                (synW3a (.classEq (.cv x) (synCsn (.cv a)))
                  (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) F (.cv b)))
                (synW3a (.classEq (.cv x) (synCsn (.cv c)))
                  (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))))))))
      p0002 p0003
  have p0005 := @gFununiq (.cv a) (.cv b) (.cv d) F
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWfun F) (synWbr (.cv a) F (.cv b)) (synWbr (.cv a) F (.cv d)))
        (.objEq b d)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWfun synWss synCin synCcompl synCnin synWnan
          synCcom synCopab synWex synCcnv synCid synWbr synCop synCun synWrex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0005
  have p0006 :=
    @gN3exp (synWfun F) (synWbr (.cv a) F (.cv b)) (synWbr (.cv a) F (.cv d))
      (.objEq b d) p0006_e00_recanon
  have p0007 := @gBreq1 (.cv a) (.cv c) (.cv d) F
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a c) (synWb (synWbr (.cv a) F (.cv d)) (synWbr (.cv c) F (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gBicomd (.objEq a c) (synWbr (.cv a) F (.cv d)) (synWbr (.cv c) F (.cv d))
      p0008_e00_recanon
  have p0009 :=
    @gAdantr (.objEq a c)
      (synWb (synWbr (.cv c) F (.cv d)) (synWbr (.cv a) F (.cv d)))
      (.classEq (.cv z) (synCsn (.cv d))) p0008
  have p0010 := @gEqeq2 (.cv z) (synCsn (.cv d)) (synCsn (.cv b))
  have p0011 := @gVex b
  have p0012 := @gSneqb (.cv b) (.cv d) p0011
  have p0013_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv b)) (synCsn (.cv d))) (.objEq b d)) :=
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
      p0012
  have p0013 :=
    @gSyl6bb (.classEq (.cv z) (synCsn (.cv d))) (.classEq (synCsn (.cv b)) (.cv z))
      (.classEq (synCsn (.cv b)) (synCsn (.cv d))) (.objEq b d) p0010 p0013_e01_recanon
  have p0014 :=
    @gAdantl (.classEq (.cv z) (synCsn (.cv d)))
      (synWb (.classEq (synCsn (.cv b)) (.cv z)) (.objEq b d)) (.objEq a c) p0013
  have p0015 :=
    @gImbi12d (synWa (.objEq a c) (.classEq (.cv z) (synCsn (.cv d))))
      (synWbr (.cv c) F (.cv d)) (synWbr (.cv a) F (.cv d))
      (.classEq (synCsn (.cv b)) (.cv z)) (.objEq b d) p0009 p0014
  have p0016 :=
    @gBiimprcd (synWa (.objEq a c) (.classEq (.cv z) (synCsn (.cv d))))
      (.imp (synWbr (.cv c) F (.cv d)) (.classEq (synCsn (.cv b)) (.cv z)))
      (.imp (synWbr (.cv a) F (.cv d)) (.objEq b d)) p0015
  have p0017 :=
    @gExp3a (.imp (synWbr (.cv a) F (.cv d)) (.objEq b d)) (.objEq a c)
      (.classEq (.cv z) (synCsn (.cv d)))
      (.imp (synWbr (.cv c) F (.cv d)) (.classEq (synCsn (.cv b)) (.cv z))) p0016
  have p0018 :=
    @gN3impd (.imp (synWbr (.cv a) F (.cv d)) (.objEq b d)) (.objEq a c)
      (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))
      (.classEq (synCsn (.cv b)) (.cv z)) p0017
  have p0019 :=
    @gSyl6 (synWfun F) (synWbr (.cv a) F (.cv b))
      (.imp (synWbr (.cv a) F (.cv d)) (.objEq b d))
      (.imp (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d))) (.classEq (synCsn (.cv b)) (.cv z)))
      p0006 p0018
  have p0020 := @gEqeq1 (.cv x) (synCsn (.cv a)) (synCsn (.cv c))
  have p0021 := @gVex a
  have p0022 := @gSneqb (.cv a) (.cv c) p0021
  have p0023_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv a)) (synCsn (.cv c))) (.objEq a c)) :=
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
      p0022
  have p0023 :=
    @gSyl6bb (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv x) (synCsn (.cv c)))
      (.classEq (synCsn (.cv a)) (synCsn (.cv c))) (.objEq a c) p0020 p0023_e01_recanon
  have p0024 :=
    @gN3anbi1d (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv x) (synCsn (.cv c)))
      (.objEq a c) (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d)) p0023
  have p0025 :=
    @gAdantr (.classEq (.cv x) (synCsn (.cv a)))
      (synWb (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d)))
        (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))))
      (.classEq (.cv y) (synCsn (.cv b))) p0024
  have p0026 := @gEqeq1 (.cv y) (synCsn (.cv b)) (.cv z)
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (synCsn (.cv b)))
        (synWb (.objEq y z) (.classEq (synCsn (.cv b)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0026
  have p0027 :=
    @gAdantl (.classEq (.cv y) (synCsn (.cv b)))
      (synWb (.objEq y z) (.classEq (synCsn (.cv b)) (.cv z)))
      (.classEq (.cv x) (synCsn (.cv a))) p0027_e00_recanon
  have p0028 :=
    @gImbi12d
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
        (synWbr (.cv c) F (.cv d)))
      (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d)))
      (.objEq y z) (.classEq (synCsn (.cv b)) (.cv z)) p0025 p0027
  have p0029 :=
    @gImbi2d
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (.imp (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d))) (.objEq y z))
      (.imp (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d))) (.classEq (synCsn (.cv b)) (.cv z)))
      (synWbr (.cv a) F (.cv b)) p0028
  have p0030 :=
    @gBiimprcd
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (.imp (synWbr (.cv a) F (.cv b)) (.imp (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))) (.objEq y z)))
      (.imp (synWbr (.cv a) F (.cv b)) (.imp
          (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d)))
            (synWbr (.cv c) F (.cv d))) (.classEq (synCsn (.cv b)) (.cv z))))
      p0029
  have p0031 :=
    @gExp3a
      (.imp (synWbr (.cv a) F (.cv b)) (.imp
          (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d)))
            (synWbr (.cv c) F (.cv d))) (.classEq (synCsn (.cv b)) (.cv z))))
      (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
      (.imp (synWbr (.cv a) F (.cv b)) (.imp (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))) (.objEq y z)))
      p0030
  have p0032 :=
    @gN3impd
      (.imp (synWbr (.cv a) F (.cv b)) (.imp
          (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d)))
            (synWbr (.cv c) F (.cv d))) (.classEq (synCsn (.cv b)) (.cv z))))
      (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
      (synWbr (.cv a) F (.cv b))
      (.imp (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d))) (.objEq y z))
      p0031
  have p0033 :=
    @gSyl (synWfun F)
      (.imp (synWbr (.cv a) F (.cv b)) (.imp
          (synW3a (.objEq a c) (.classEq (.cv z) (synCsn (.cv d)))
            (synWbr (.cv c) F (.cv d))) (.classEq (synCsn (.cv b)) (.cv z))))
      (.imp (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
          (synWbr (.cv a) F (.cv b))) (.imp (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))) (.objEq y z)))
      p0019 p0032
  have p0034 :=
    @gImp3a (synWfun F)
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (synWbr (.cv a) F (.cv b)))
      (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
        (synWbr (.cv c) F (.cv d)))
      (.objEq y z) p0033
  have p0035 :=
    @gExlimdvv (synWfun F)
      (synWa (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
          (synWbr (.cv a) F (.cv b)))
        (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv z) (synCsn (.cv d)))
          (synWbr (.cv c) F (.cv d))))
      (.objEq y z) c d dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0034
  have p0036 :=
    @gExlimdvv (synWfun F)
      (synWex c (synWex d (synWa (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) F (.cv b)))
            (synW3a (.classEq (.cv x) (synCsn (.cv c)))
              (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))))))
      (.objEq y z) a b dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 p0035
  have p0037 :=
    @gSyl5bi
      (synWa (synWbr (.cv x) (synCsi F) (.cv y)) (synWbr (.cv x) (synCsi F) (.cv z)))
      (synWex a (synWex b (synWex c (synWex d (synWa
                (synW3a (.classEq (.cv x) (synCsn (.cv a)))
                  (.classEq (.cv y) (synCsn (.cv b))) (synWbr (.cv a) F (.cv b)))
                (synW3a (.classEq (.cv x) (synCsn (.cv c)))
                  (.classEq (.cv z) (synCsn (.cv d))) (synWbr (.cv c) F (.cv d))))))))
      (synWfun F) (.objEq y z) p0004 p0036
  have p0038 :=
    @gAlrimiv (synWfun F)
      (.imp (synWa (synWbr (.cv x) (synCsi F) (.cv y)) (synWbr (.cv x) (synCsi F) (.cv z)))
        (.objEq y z))
      z dv_cache_0029 p0037
  have p0039 :=
    @gAlrimivv (synWfun F)
      (.all z (.imp (synWa (synWbr (.cv x) (synCsi F) (.cv y))
            (synWbr (.cv x) (synCsi F) (.cv z))) (.objEq y z)))
      x y dv_cache_0030 dv_cache_0031 p0038
  have p0040 :=
    @gDffun2 x y z (synCsi F) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
  have p0041 :=
    @gSylibr (synWfun F)
      (.all x (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCsi F) (.cv y))
                (synWbr (.cv x) (synCsi F) (.cv z))) (.objEq y z)))))
      (synWfun (synCsi F)) p0039 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_rnsi`. -/
@[expose]
noncomputable def gRnsi (R : Class) :
    Nominal.NPrf (.classEq (synCrn (synCsi R)) (synCpw1 (synCrn R))) :=
  by
  have p0000 := @gCnvsi R
  have p0001 := @gDmeqi (synCcnv (synCsi R)) (synCsi (synCcnv R)) p0000
  have p0002 := @gDmsi (synCcnv R)
  have p0003 :=
    @gEqtri (synCdm (synCcnv (synCsi R))) (synCdm (synCsi (synCcnv R)))
      (synCpw1 (synCdm (synCcnv R))) p0001 p0002
  have p0004 := @gDfrn4 (synCsi R)
  have p0005 := @gDfrn4 R
  have p0006 := @gPw1eq (synCrn R) (synCdm (synCcnv R))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gN3eqtr4i (synCdm (synCcnv (synCsi R))) (synCpw1 (synCdm (synCcnv R)))
      (synCrn (synCsi R)) (synCpw1 (synCrn R)) p0003 p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_op1std`. -/
@[expose]
noncomputable def gOp1std (A : Class) (B : Class) (C : Class)
    (hyp_op1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_op1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.imp (.classEq C (synCop A B)) (.classEq (synCfv (synC1st) C) A)) :=
  by
  have p0000 := @gFveq2 C (synCop A B) (synC1st)
  have p0001 := @gOpfv1st A B hyp_op1st_1 hyp_op1st_2
  have p0002 :=
    @gSyl6eq (.classEq C (synCop A B)) (synCfv (synC1st) C)
      (synCfv (synC1st) (synCop A B)) A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_op2ndd`. -/
@[expose]
noncomputable def gOp2ndd (A : Class) (B : Class) (C : Class)
    (hyp_op1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_op1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.imp (.classEq C (synCop A B)) (.classEq (synCfv (synC2nd) C) B)) :=
  by
  have p0000 := @gFveq2 C (synCop A B) (synC2nd)
  have p0001 := @gOpfv2nd A B hyp_op1st_1 hyp_op1st_2
  have p0002 :=
    @gSyl6eq (.classEq C (synCop A B)) (synCfv (synC2nd) C)
      (synCfv (synC2nd) (synCop A B)) B p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_oveq1`. -/
@[expose]
noncomputable def gOveq1 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCo A F C) (synCo B F C))) :=
  by
  have p0000 := @gOpeq1 A B C
  have p0001 := @gFveq2d (.classEq A B) (synCop A C) (synCop B C) F p0000
  have p0002 := (Nominal.classEqRefl (synCo A F C))
  have p0003 := (Nominal.classEqRefl (synCo B F C))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCfv F (synCop A C)) (synCfv F (synCop B C))
      (synCo A F C) (synCo B F C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_oveq2`. -/
@[expose]
noncomputable def gOveq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCo C F A) (synCo C F B))) :=
  by
  have p0000 := @gOpeq2 A B C
  have p0001 := @gFveq2d (.classEq A B) (synCop C A) (synCop C B) F p0000
  have p0002 := (Nominal.classEqRefl (synCo C F A))
  have p0003 := (Nominal.classEqRefl (synCo C F B))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCfv F (synCop C A)) (synCfv F (synCop C B))
      (synCo C F A) (synCo C F B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_oveq12`. -/
@[expose]
noncomputable def gOveq12 (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCo A F C) (synCo B F D))) :=
  by
  have p0000 := @gOveq1 A B C F
  have p0001 := @gOveq2 C D B F
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCo A F C) (synCo B F C) (synCo B F D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_oveq2d`. -/
@[expose]
noncomputable def gOveq2d (ph : Wff) (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_oveq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCo C F A) (synCo C F B))) :=
  by
  have p0000 := @gOveq2 A B C F
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCo C F A) (synCo C F B)) hyp_oveq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ovex`. -/
@[expose]
noncomputable def gOvex (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.classMem (synCo A F B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCo A F B))
  have p0001 := @gFvex (synCop A B) F
  have p0002 := @gEqeltri (synCo A F B) (synCfv F (synCop A B)) (synCvv) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfoprab2`. -/
@[expose]
noncomputable def gDfoprab2 (ph : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCoprab x y z ph) (synCopab w z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_ph : v ∉ ph.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_v_ne_w : v ≠ w := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
  have dv_cache_0001 : w ∉ ((synCop (.cv x) (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_w_x, dv_w_y, or_false, not_false_eq_true])
  have dv_cache_0002 :
    w ∉ ((synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_v, dv_w_x, dv_w_y, dv_w_z, dv_ph_w, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv v) (synCop (.cv w) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, (Ne.symm dv_w_x), dv_x_z, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv v) (synCop (.cv w) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_v, (Ne.symm dv_w_y), dv_y_z, or_false,
          not_false_eq_true])
  have dv_cache_0005 : v ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_ph, not_false_eq_true])
  have dv_cache_0006 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0007 : v ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0008 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0009 :
    v ∉
      ((synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_x,
          fresh_v_ne_y, fresh_v_not_ph, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0011 : z ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show z ≠ v from (by exact fresh_z_ne_v))
  have p0000 :=
    @gExcom
      (synWex x (synWex y (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
            (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      z w
  have p0001 :=
    @gExrot4
      (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
        (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))
      z w x y
  have p0002 :=
    @gAn12 (.classEq (.cv v) (synCop (.cv w) (.cv z)))
      (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph
  have p0003 :=
    @gExbii
      (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
        (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))
      (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y)))
        (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z))) ph))
      w p0002
  have p0004 := @gVex x
  have p0005 := @gVex y
  have p0006 := @gOpex (.cv x) (.cv y) p0004 p0005
  have p0007 := @gOpeq1 (.cv w) (synCop (.cv x) (.cv y)) (.cv z)
  have p0008 :=
    @gEqeq2d (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synCop (.cv w) (.cv z))
      (synCop (synCop (.cv x) (.cv y)) (.cv z)) (.cv v) p0007
  have p0009 :=
    @gAnbi1d (.classEq (.cv w) (synCop (.cv x) (.cv y)))
      (.classEq (.cv v) (synCop (.cv w) (.cv z)))
      (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph p0008
  have p0010 :=
    @gCeqsexv (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z))) ph)
      (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph) w
      (synCop (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002 p0006 p0009
  have p0011 :=
    @gBitri
      (synWex w (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
          (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))
      (synWex w (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y)))
          (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z))) ph)))
      (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph) p0003
      p0010
  have p0012 :=
    @gN3exbii
      (synWex w (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
          (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))
      (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph) x y z
      p0011
  have p0013 :=
    @gBitri
      (synWex z (synWex w (synWex x (synWex y
              (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
                (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))))
      (synWex x (synWex y (synWex z (synWex w
              (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
                (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))))
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      p0001 p0012
  have p0014 :=
    @gN1942vv (.classEq (.cv v) (synCop (.cv w) (.cv z)))
      (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph) x y dv_cache_0003
      dv_cache_0004
  have p0015 :=
    @gN2exbii
      (synWex x (synWex y (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
            (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      w z p0014
  have p0016 :=
    @gN3bitr3i
      (synWex z (synWex w (synWex x (synWex y
              (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
                (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))))
      (synWex w (synWex z (synWex x (synWex y
              (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
                (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))))
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      (synWex w (synWex z (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z))) (synWex x
              (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))))
      p0000 p0013 p0015
  have p0017 :=
    @gAbbii
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      (synWex w (synWex z (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z))) (synWex x
              (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))))
      v p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOprab ph x y z v
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))) w z
      v dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0020 :=
    @gN3eqtr4i
      (.cab v (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv v) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph)))))
      (.cab v (synWex w (synWex z (synWa (.classEq (.cv v) (synCop (.cv w) (.cv z)))
              (synWex x
                (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))))
      (synCoprab x y z ph)
      (synCopab w z
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      p0017 p0018 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_oprabbid`. -/
@[expose]
noncomputable def gOprabbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (_dv_x_z : x ≠ z) (_dv_y_z : y ≠ z)
    (hyp_oprabbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_oprabbid_2 : Nominal.NPrf (synWnf y ph))
    (hyp_oprabbid_3 : Nominal.NPrf (synWnf z ph))
    (hyp_oprabbid_4 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCoprab x y z ps) (synCoprab x y z ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_ch : w ∉ ch.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0002 : w ∉ (ps).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ps, not_false_eq_true])
  have dv_cache_0003 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0004 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0005 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : w ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ch, not_false_eq_true])
  have p0000 :=
    @gAnbi2d ph ps ch (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z)))
      hyp_oprabbid_4
  have p0001 :=
    @gExbid ph (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ps)
      (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ch) z
      hyp_oprabbid_3 p0000
  have p0002 :=
    @gExbid ph
      (synWex z (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ps))
      (synWex z (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ch))
      y hyp_oprabbid_2 p0001
  have p0003 :=
    @gExbid ph
      (synWex y (synWex z
          (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ps)))
      (synWex y (synWex z
          (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ch)))
      x hyp_oprabbid_1 p0002
  have p0004 :=
    @gAbbidv ph
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ps))))
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ch))))
      w dv_cache_0001 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOprab ps x y z w
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOprab ch x y z w
      dv_cache_0006 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @gN3eqtr4g ph
      (.cab w (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ps)))))
      (.cab w (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ch)))))
      (synCoprab x y z ps) (synCoprab x y z ch) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_oprabbidv`. -/
@[expose]
noncomputable def gOprabbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_oprabbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCoprab x y z ps) (synCoprab x y z ch))) :=
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
  have dv_cache_0003 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gNfv ph x dv_cache_0001
  have p0001 := @gNfv ph y dv_cache_0002
  have p0002 := @gNfv ph z dv_cache_0003
  have p0003 :=
    @gOprabbid ph ps ch x y z dv_cache_0004 dv_cache_0005 p0000 p0001 p0002
      hyp_oprabbidv_1
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_oprabbii`. -/
@[expose]
noncomputable def gOprabbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_oprabbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (.classEq (synCoprab x y z ph) (synCoprab x y z ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv w) (.cv w))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv w) (.cv w))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv w) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, or_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gEqid (.cv w)
  have p0001 := @gA1i (synWb ph ps) (.classEq (.cv w) (.cv w)) hyp_oprabbii_1
  have p0002 :=
    @gOprabbidv (.classEq (.cv w) (.cv w)) ph ps x y z dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0001
  have p0003 := Nominal.mp p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cbvoprab12`. -/
@[expose]
noncomputable def gCbvoprab12 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (w : Var) (v : Var) (dv_v_w : v ≠ w) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y)
    (dv_v_z : v ≠ z) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_cbvoprab12_1 : Nominal.NPrf (synWnf w ph))
    (hyp_cbvoprab12_2 : Nominal.NPrf (synWnf v ph))
    (hyp_cbvoprab12_3 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvoprab12_4 : Nominal.NPrf (synWnf y ps))
    (hyp_cbvoprab12_5 : Nominal.NPrf (.imp (synWa (.objEq x w) (.objEq y v)) (synWb ph ps))) :
    Nominal.NPrf (.classEq (synCoprab x y z ph) (synCoprab w v z ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
        ({ w } : Finset Var) ∪
      ({ v } : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_ph : u ∉ ph.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_u_not_ps : u ∉ ps.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_u : w ≠ u := Ne.symm fresh_u_ne_w
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have dv_cache_0001 : w ∉ ((Wff.classEq (.cv u) (synCop (.cv x) (.cv y)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, dv_w_x, dv_w_y, or_false,
          not_false_eq_true])
  have dv_cache_0002 : v ∉ ((Wff.classEq (.cv u) (synCop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, dv_v_x, dv_v_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv u) (synCop (.cv w) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, (Ne.symm dv_w_x), (Ne.symm dv_v_x),
          or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv u) (synCop (.cv w) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_u, (Ne.symm dv_w_y), (Ne.symm dv_v_y),
          or_false, not_false_eq_true])
  have dv_cache_0005 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact dv_v_x))
  have dv_cache_0006 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ w from (by exact dv_v_w))
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ w from (by exact Ne.symm dv_w_y))
  have dv_cache_0009 : u ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_ph, not_false_eq_true])
  have dv_cache_0010 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0011 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0012 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show u ≠ z from (by exact fresh_u_ne_z))
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
  have dv_cache_0015 : u ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_ps, not_false_eq_true])
  have dv_cache_0016 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0017 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0018 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show w ≠ z from (by exact dv_w_z))
  have dv_cache_0019 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show v ≠ z from (by exact dv_v_z))
  have p0000 := @gNfv (.classEq (.cv u) (synCop (.cv x) (.cv y))) w dv_cache_0001
  have p0001 :=
    @gNfan (.classEq (.cv u) (synCop (.cv x) (.cv y))) ph w p0000 hyp_cbvoprab12_1
  have p0002 := @gNfv (.classEq (.cv u) (synCop (.cv x) (.cv y))) v dv_cache_0002
  have p0003 :=
    @gNfan (.classEq (.cv u) (synCop (.cv x) (.cv y))) ph v p0002 hyp_cbvoprab12_2
  have p0004 := @gNfv (.classEq (.cv u) (synCop (.cv w) (.cv v))) x dv_cache_0003
  have p0005 :=
    @gNfan (.classEq (.cv u) (synCop (.cv w) (.cv v))) ps x p0004 hyp_cbvoprab12_3
  have p0006 := @gNfv (.classEq (.cv u) (synCop (.cv w) (.cv v))) y dv_cache_0004
  have p0007 :=
    @gNfan (.classEq (.cv u) (synCop (.cv w) (.cv v))) ps y p0006 hyp_cbvoprab12_4
  have p0008 := @gOpeq12 (.cv x) (.cv w) (.cv y) (.cv v)
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq x w) (.objEq y v))
        (.classEq (synCop (.cv x) (.cv y)) (synCop (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCop synCun synCnin synWnan synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gEqeq2d (synWa (.objEq x w) (.objEq y v)) (synCop (.cv x) (.cv y))
      (synCop (.cv w) (.cv v)) (.cv u) p0009_e00_recanon
  have p0010 :=
    @gAnbi12d (synWa (.objEq x w) (.objEq y v))
      (.classEq (.cv u) (synCop (.cv x) (.cv y)))
      (.classEq (.cv u) (synCop (.cv w) (.cv v))) ph ps p0009 hyp_cbvoprab12_5
  have p0011 :=
    @gCbvex2 (synWa (.classEq (.cv u) (synCop (.cv x) (.cv y))) ph)
      (synWa (.classEq (.cv u) (synCop (.cv w) (.cv v))) ps) x y w v dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 p0001 p0003 p0005 p0007 p0010
  have p0012 :=
    @gOpabbii
      (synWex x (synWex y (synWa (.classEq (.cv u) (synCop (.cv x) (.cv y))) ph)))
      (synWex w (synWex v (synWa (.classEq (.cv u) (synCop (.cv w) (.cv v))) ps))) u z
      p0011
  have p0013 :=
    @gDfoprab2 ph x y z u dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014
  have p0014 :=
    @gDfoprab2 ps w v z u dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0012
      dv_cache_0018 dv_cache_0019
  have p0015 :=
    @gN3eqtr4i
      (synCopab u z
        (synWex x (synWex y (synWa (.classEq (.cv u) (synCop (.cv x) (.cv y))) ph))))
      (synCopab u z
        (synWex w (synWex v (synWa (.classEq (.cv u) (synCop (.cv w) (.cv v))) ps))))
      (synCoprab x y z ph) (synCoprab w v z ps) p0012 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_dmoprab`. -/
@[expose]
noncomputable def gDmoprab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCdm (synCoprab x y z ph)) (synCopab x y (synWex z ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0002 : w ≠ x := by
    clear dv_cache_0001
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0003 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0004 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv w) (synCop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, (Ne.symm dv_x_z), (Ne.symm dv_y_z),
          or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((synWex z ph)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_erase,
          fresh_w_not_ph, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0010 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have p0000 :=
    @gDfoprab2 ph x y z w dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gDmeqi (synCoprab x y z ph)
      (synCopab w z
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      p0000
  have p0002 :=
    @gDmopab
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))) w z
      dv_cache_0004
  have p0003 := @gExrot3 (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph) z x y
  have p0004 :=
    @gN1942v (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph z dv_cache_0007
  have p0005 :=
    @gN2exbii (synWex z (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))
      (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synWex z ph)) x y p0004
  have p0006 :=
    @gBitri
      (synWex z
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      (synWex x
        (synWex y (synWex z (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      (synWex x
        (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synWex z ph))))
      p0003 p0005
  have p0007 :=
    @gAbbii
      (synWex z
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      (synWex x
        (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synWex z ph))))
      w p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab (synWex z ph)
      x y w dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0009 :=
    @gEqtr4i
      (.cab w (synWex z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))
      (.cab w (synWex x (synWex y
            (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) (synWex z ph)))))
      (synCopab x y (synWex z ph)) p0007 p0008
  have p0010 :=
    @gN3eqtri (synCdm (synCoprab x y z ph))
      (synCdm (synCopab w z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))
      (.cab w (synWex z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))
      (synCopab x y (synWex z ph)) p0001 p0002 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_eloprabga`. -/
@[expose]
noncomputable def gEloprabga (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_eloprabga_1 : Nominal.NPrf
        (.imp (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
        (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
                A.fv ∪
              B.fv ∪
            C.fv ∪
          V.fv ∪
        W.fv ∪
      X.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv w) (synCop (synCop A B) C))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_A_x, dv_B_x, dv_C_x, or_false,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv w) (synCop (synCop A B) C))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, dv_A_y, dv_B_y, dv_C_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv w) (synCop (synCop A B) C))).fv :=
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
          Finset.mem_singleton, fresh_z_ne_w, dv_A_z, dv_B_z, dv_C_z, or_false,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0005 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0006 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0007 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show w ≠ z from (by exact fresh_w_ne_z))
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
        simp only [dv_A_x, not_false_eq_true])
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
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0010 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Wff.classEq (.cv z) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_z, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classEq (.cv z) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_y_z, dv_C_y, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classEq (.cv x) A)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Wff.classEq (.cv x) A)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), dv_A_z, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Wff.classEq (.cv y) B)).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classEq (.cv y) B)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_y_z), dv_B_z, or_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0018 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0019 : x ∉ (ps).fv :=
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
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0020 : y ∉ (ps).fv :=
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
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0021 : z ∉ (ps).fv :=
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
        simp only [dv_ps_z, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((synCop (synCop A B) C)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_w_not_A, fresh_w_not_B, fresh_w_not_C, or_false, not_false_eq_true])
  have dv_cache_0023 :
    w ∉
      ((Wff.imp (synW3a (.classMem A (synCvv)) (.classMem B (synCvv))
            (.classMem C (synCvv)))
          (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coprab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_C, fresh_w_not_A,
          fresh_w_not_B, fresh_w_not_ph, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_ps,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gElex A V
  have p0001 := @gElex B W
  have p0002 := @gElex C X
  have p0003 := @gOpexg A B (synCvv) (synCvv)
  have p0004 := @gOpexg (synCop A B) C (synCvv) (synCvv)
  have p0005 :=
    @gSylan (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCop A B) (synCvv)) (.classMem C (synCvv))
      (.classMem (synCop (synCop A B) C) (synCvv)) p0003 p0004
  have p0006 :=
    @gN3impa (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
      (.classMem (synCop (synCop A B) C) (synCvv)) p0005
  have p0007 :=
    @gEqeq1 (.cv w) (synCop (synCop A B) C) (synCop (synCop (.cv x) (.cv y)) (.cv z))
  have p0008 :=
    @gEqcom (synCop (synCop A B) C) (synCop (synCop (.cv x) (.cv y)) (.cv z))
  have p0009 := @gOpth (.cv x) (.cv y) A B
  have p0010 :=
    @gAnbi1i (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (.cv z) C) p0009
  have p0011 := @gOpth (synCop (.cv x) (.cv y)) (.cv z) (synCop A B) C
  have p0012 :=
    (Nominal.biimpRefl (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))
  have p0013 :=
    @gN3bitr4i
      (synWa (.classEq (synCop (.cv x) (.cv y)) (synCop A B)) (.classEq (.cv z) C))
      (synWa (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (.cv z) C))
      (.classEq (synCop (synCop (.cv x) (.cv y)) (.cv z)) (synCop (synCop A B) C))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0010 p0011
      p0012
  have p0014 :=
    @gBitri
      (.classEq (synCop (synCop A B) C) (synCop (synCop (.cv x) (.cv y)) (.cv z)))
      (.classEq (synCop (synCop (.cv x) (.cv y)) (.cv z)) (synCop (synCop A B) C))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0008 p0013
  have p0015 :=
    @gSyl6bb (.classEq (.cv w) (synCop (synCop A B) C))
      (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z)))
      (.classEq (synCop (synCop A B) C) (synCop (synCop (.cv x) (.cv y)) (.cv z)))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0007 p0014
  have p0016 :=
    @gAnbi1d (.classEq (.cv w) (synCop (synCop A B) C))
      (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z)))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph p0015
  have p0017 :=
    @gPm532i (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph
      ps hyp_eloprabga_1
  have p0018 :=
    @gSyl6bb (.classEq (.cv w) (synCop (synCop A B) C))
      (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph)
      (synWa (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph)
      (synWa (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)
      p0016 p0017
  have p0019 :=
    @gN3exbidv (.classEq (.cv w) (synCop (synCop A B) C))
      (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph)
      (synWa (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)
      x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 p0018
  have p0020 :=
    @gAdantl (.classEq (.cv w) (synCop (synCop A B) C))
      (synWb (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
        (synWex x (synWex y (synWex z (synWa
                (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)))))
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      p0019
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOprab ph x y z w
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0022 :=
    @gEleq2i (synCoprab x y z ph)
      (.cab w (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph)))))
      (.cv w) p0021
  have p0023 :=
    @gAbid
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      w
  have p0024 :=
    @gBitr2i (.classMem (.cv w) (synCoprab x y z ph))
      (.classMem (.cv w) (.cab w (synWex x (synWex y (synWex z
                (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))))
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      p0022 p0023
  have p0025 := @gEleq1 (.cv w) (synCop (synCop A B) C) (synCoprab x y z ph)
  have p0026 :=
    @gSyl5bb
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      (.classMem (.cv w) (synCoprab x y z ph))
      (.classEq (.cv w) (synCop (synCop A B) C))
      (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) p0024 p0025
  have p0027 :=
    @gAdantl (.classEq (.cv w) (synCop (synCop A B) C))
      (synWb (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
        (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)))
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      p0026
  have p0028 := @gIsset x A dv_cache_0008
  have p0029 := @gIsset y B dv_cache_0009
  have p0030 := @gIsset z C dv_cache_0010
  have p0031 :=
    @gN3anbi123i (.classMem A (synCvv)) (synWex x (.classEq (.cv x) A))
      (.classMem B (synCvv)) (synWex y (.classEq (.cv y) B)) (.classMem C (synCvv))
      (synWex z (.classEq (.cv z) C)) p0028 p0029 p0030
  have p0032 :=
    @gEeeanv (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C) x y z
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018
  have p0033 :=
    @gBitr4i
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synW3a (synWex x (.classEq (.cv x) A)) (synWex y (.classEq (.cv y) B))
        (synWex z (.classEq (.cv z) C)))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      p0031 p0032
  have p0034 :=
    @gBiimpi
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      p0033
  have p0035 :=
    @gBiantrurd
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      ps p0034
  have p0036 :=
    @gN1941vvv (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      ps x y z dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0037 :=
    @gSyl6rbbr
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))) ps
      (synWa (synWex x (synWex y (synWex z
              (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))) ps)
      (synWex x (synWex y (synWex z (synWa
              (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))
      p0035 p0036
  have p0038 :=
    @gAdantr
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWb (synWex x (synWex y (synWex z (synWa
                (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))
        ps)
      (.classEq (.cv w) (synCop (synCop A B) C)) p0037
  have p0039 :=
    @gN3bitr3d
      (synWa (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
        (.classEq (.cv w) (synCop (synCop A B) C)))
      (synWex x (synWex y (synWex z
            (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))
      (synWex x (synWex y (synWex z (synWa
              (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))
      (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps p0020 p0027 p0038
  have p0040 :=
    @gExpcom
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classEq (.cv w) (synCop (synCop A B) C))
      (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps) p0039
  have p0041 :=
    @gVtocleg
      (.imp (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
        (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps))
      w (synCop (synCop A B) C) (synCvv) dv_cache_0022 dv_cache_0023 p0040
  have p0042 :=
    @gMpcom (.classMem (synCop (synCop A B) C) (synCvv))
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps) p0006 p0041
  have p0043 :=
    @gSyl3an (.classMem A V) (.classMem A (synCvv)) (.classMem B W)
      (.classMem B (synCvv)) (.classMem C X) (.classMem C (synCvv))
      (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) ps) p0000 p0001
      p0002 p0042
  exact p0043

/-- Checked nominal proof certificate identified upstream as `g_eloprabg`. -/
@[expose]
noncomputable def gEloprabg (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class)
    (X : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_th_x : x ∉ th.fv) (dv_th_y : y ∉ th.fv)
    (dv_th_z : z ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_eloprabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_eloprabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_eloprabg_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (synWb ch th))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
        (synWb (.classMem (synCop (synCop A B) C) (synCoprab x y z ph)) th)) :=
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
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
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
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0010 : x ∉ (th).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_th_x, not_false_eq_true])
  have dv_cache_0011 : y ∉ (th).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_th_y, not_false_eq_true])
  have dv_cache_0012 : z ∉ (th).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_th_z, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @gSyl3an9b (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch (.classEq (.cv z) C) th
      hyp_eloprabg_1 hyp_eloprabg_2 hyp_eloprabg_3
  have p0001 :=
    @gEloprabga ph th x y z A B C V W X dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_funoprabg`. -/
@[expose]
noncomputable def gFunoprabg (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.all x (.all y (synWmo z ph))) (synWfun (synCoprab x y z ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
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
  have dv_cache_0004 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show z ≠ x from (by exact Ne.symm dv_x_z))
  have dv_cache_0005 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ y from (by exact Ne.symm dv_y_z))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0007 : w ∉ ((Wff.all x (.all y (synWmo z ph)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo, Finset.mem_erase,
          fresh_w_not_ph, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0009 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0010 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0011 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0012 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0013 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @gMosubopt ph z x y (.cv w) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gAlrimiv (.all x (.all y (synWmo z ph)))
      (synWmo z
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      w dv_cache_0007 p0000
  have p0002 :=
    @gDfoprab2 ph x y z w dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
  have p0003 :=
    @gFuneqi (synCoprab x y z ph)
      (synCopab w z
        (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))))
      p0002
  have p0004 :=
    @gFunopab
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph))) w z
      dv_cache_0011
  have p0005 :=
    @gBitr2i (synWfun (synCoprab x y z ph))
      (synWfun (synCopab w z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))
      (.all w (synWmo z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))
      p0003 p0004
  have p0006 :=
    @gSylib (.all x (.all y (synWmo z ph)))
      (.all w (synWmo z (synWex x
            (synWex y (synWa (.classEq (.cv w) (synCop (.cv x) (.cv y))) ph)))))
      (synWfun (synCoprab x y z ph)) p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_funoprab`. -/
@[expose]
noncomputable def gFunoprab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_funoprab_1 : Nominal.NPrf (synWmo z ph)) :
    Nominal.NPrf (synWfun (synCoprab x y z ph)) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gGen2 (synWmo z ph) x y hyp_funoprab_1
  have p0001 := @gFunoprabg ph x y z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fnoprabg`. -/
@[expose]
noncomputable def gFnoprabg (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.all x (.all y (.imp ph (synWeu z ps))))
        (synWfn (synCoprab x y z (synWa ph ps)) (synCopab x y ph))) :=
  by
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gEumo ps z
  have p0001 := @gImim2i (synWeu z ps) (synWmo z ps) ph p0000
  have p0002 := @gMoanimv ph ps z dv_cache_0001
  have p0003 :=
    @gSylibr (.imp ph (synWeu z ps)) (.imp ph (synWmo z ps)) (synWmo z (synWa ph ps))
      p0001 p0002
  have p0004 := @gN2alimi (.imp ph (synWeu z ps)) (synWmo z (synWa ph ps)) x y p0003
  have p0005 :=
    @gFunoprabg (synWa ph ps) x y z dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gSyl (.all x (.all y (.imp ph (synWeu z ps))))
      (.all x (.all y (synWmo z (synWa ph ps))))
      (synWfun (synCoprab x y z (synWa ph ps))) p0004 p0005
  have p0007 := @gDmoprab (synWa ph ps) x y z dv_cache_0003 dv_cache_0004
  have p0008 := @gNfa1 (.all y (.imp ph (synWeu z ps))) x
  have p0009 := @gNfa2 (.imp ph (synWeu z ps)) y x
  have p0010 := @gSimpl ph ps
  have p0011 := @gExlimiv (synWa ph ps) ph z dv_cache_0001 p0010
  have p0012 := @gEuex ps z
  have p0013 := @gImim2i (synWeu z ps) (synWex z ps) ph p0012
  have p0014 := @gAncld (.imp ph (synWeu z ps)) ph (synWex z ps) p0013
  have p0015 := @gN1942v ph ps z dv_cache_0001
  have p0016 :=
    @gSyl6ibr (.imp ph (synWeu z ps)) ph (synWa ph (synWex z ps))
      (synWex z (synWa ph ps)) p0014 p0015
  have p0017 :=
    @gImpbid2 (.imp ph (synWeu z ps)) (synWex z (synWa ph ps)) ph p0011 p0016
  have p0018 :=
    @gSps (.imp ph (synWeu z ps)) (synWb (synWex z (synWa ph ps)) ph) y p0017
  have p0019 :=
    @gSps (.all y (.imp ph (synWeu z ps))) (synWb (synWex z (synWa ph ps)) ph) x
      p0018
  have p0020 :=
    @gOpabbid (.all x (.all y (.imp ph (synWeu z ps)))) (synWex z (synWa ph ps)) ph x
      y p0008 p0009 p0019
  have p0021 :=
    @gSyl5eq (.all x (.all y (.imp ph (synWeu z ps))))
      (synCdm (synCoprab x y z (synWa ph ps)))
      (synCopab x y (synWex z (synWa ph ps))) (synCopab x y ph) p0007 p0020
  have p0022 :=
    (Nominal.biimpRefl (synWfn (synCoprab x y z (synWa ph ps)) (synCopab x y ph)))
  have p0023 :=
    @gSylanbrc (.all x (.all y (.imp ph (synWeu z ps))))
      (synWfun (synCoprab x y z (synWa ph ps)))
      (.classEq (synCdm (synCoprab x y z (synWa ph ps))) (synCopab x y ph))
      (synWfn (synCoprab x y z (synWa ph ps)) (synCopab x y ph)) p0006 p0021 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_fnoprab`. -/
@[expose]
noncomputable def gFnoprab (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_fnoprab_1 : Nominal.NPrf (.imp ph (synWeu z ps))) :
    Nominal.NPrf (synWfn (synCoprab x y z (synWa ph ps)) (synCopab x y ph)) :=
  by
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_z, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gGen2 (.imp ph (synWeu z ps)) x y hyp_fnoprab_1
  have p0001 :=
    @gFnoprabg ph ps x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ovigg`. -/
@[expose]
noncomputable def gOvigg (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (F : Class) (V : Class) (W : Class) (X : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_ovigg_1 : Nominal.NPrf
        (.imp (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (synWb ph ps)))
    (hyp_ovigg_4 : Nominal.NPrf (synWmo z ph))
    (hyp_ovigg_5 : Nominal.NPrf (.classEq F (synCoprab x y z ph))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
        (.imp ps (.classEq (synCo A F B) C))) :=
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
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
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
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0010 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0011 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0012 : z ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_z, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @gEloprabga ph ps x y z A B C V W X dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      hyp_ovigg_1
  have p0001 := @gFunoprab ph x y z dv_cache_0013 dv_cache_0014 dv_cache_0015 hyp_ovigg_4
  have p0002 := @gFunopfv (synCop A B) C (synCoprab x y z ph)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gSyl6bir (synW3a (.classMem A V) (.classMem B W) (.classMem C X)) ps
      (.classMem (synCop (synCop A B) C) (synCoprab x y z ph))
      (.classEq (synCfv (synCoprab x y z ph) (synCop A B)) C) p0000 p0003
  have p0005 := (Nominal.classEqRefl (synCo A F B))
  have p0006 := @gFveq1i (synCop A B) F (synCoprab x y z ph) hyp_ovigg_5
  have p0007 :=
    @gEqtri (synCo A F B) (synCfv F (synCop A B))
      (synCfv (synCoprab x y z ph) (synCop A B)) p0005 p0006
  have p0008 :=
    @gEqeq1i (synCo A F B) (synCfv (synCoprab x y z ph) (synCop A B)) C p0007
  have p0009 :=
    @gSyl6ibr (synW3a (.classMem A V) (.classMem B W) (.classMem C X)) ps
      (.classEq (synCfv (synCoprab x y z ph) (synCop A B)) C)
      (.classEq (synCo A F B) C) p0004 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ovig`. -/
@[expose]
noncomputable def gOvig (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_ovig_1 : Nominal.NPrf
        (.imp (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (synWb ph ps)))
    (hyp_ovig_2 : Nominal.NPrf
        (.imp (synWa (.classMem (.cv x) R) (.classMem (.cv y) S)) (synWmo z ph)))
    (hyp_ovig_3 : Nominal.NPrf (.classEq F (synCoprab x y z
            (synWa (synWa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph)))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A R) (.classMem B S) (.classMem C D))
        (.imp ps (.classEq (synCo A F B) C))) :=
  by
  have dv_cache_0001 : z ∉ ((synWa (.classMem (.cv x) R) (.classMem (.cv y) S))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), dv_R_z, (Ne.symm dv_y_z), dv_S_z,
          or_false, not_false_eq_true])
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
  have dv_cache_0004 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
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
  have dv_cache_0007 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
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
        simp only [dv_C_x, not_false_eq_true])
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
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0010 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synWa (synWa (.classMem A R) (.classMem B S)) ps)).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_A_x, dv_R_x,
          dv_B_x, dv_S_x, dv_ps_x, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synWa (synWa (.classMem A R) (.classMem B S)) ps)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_A_y, dv_R_y,
          dv_B_y, dv_S_y, dv_ps_y, or_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((synWa (synWa (.classMem A R) (.classMem B S)) ps)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_A_z, dv_R_z,
          dv_B_z, dv_S_z, dv_ps_z, or_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0015 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0016 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gN3simpa (.classMem A R) (.classMem B S) (.classMem C D)
  have p0001 := @gEleq1 (.cv x) A R
  have p0002 := @gEleq1 (.cv y) B S
  have p0003 :=
    @gBi2anan9 (.classEq (.cv x) A) (.classMem (.cv x) R) (.classMem A R)
      (.classEq (.cv y) B) (.classMem (.cv y) S) (.classMem B S) p0001 p0002
  have p0004 :=
    @gN3adant3 (.classEq (.cv x) A) (.classEq (.cv y) B)
      (synWb (synWa (.classMem (.cv x) R) (.classMem (.cv y) S))
        (synWa (.classMem A R) (.classMem B S)))
      (.classEq (.cv z) C) p0003
  have p0005 :=
    @gAnbi12d (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      (synWa (.classMem (.cv x) R) (.classMem (.cv y) S))
      (synWa (.classMem A R) (.classMem B S)) ph ps p0004 hyp_ovig_1
  have p0006 :=
    @gMoanimv (synWa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph z dv_cache_0001
  have p0007 :=
    @gMpbir (synWmo z (synWa (synWa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph))
      (.imp (synWa (.classMem (.cv x) R) (.classMem (.cv y) S)) (synWmo z ph))
      hyp_ovig_2 p0006
  have p0008 :=
    @gOvigg (synWa (synWa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph)
      (synWa (synWa (.classMem A R) (.classMem B S)) ps) x y z A B C F R S D
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 p0005 p0007 hyp_ovig_3
  have p0009 :=
    @gMpand (synW3a (.classMem A R) (.classMem B S) (.classMem C D))
      (synWa (.classMem A R) (.classMem B S)) ps (.classEq (synCo A F B) C) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ov2ag`. -/
@[expose]
noncomputable def gOv2ag (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (R : Class) (S : Class) (F : Class) (H : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (dv_R_z : z ∉ R.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_ov2ag_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq R S)))
    (hyp_ov2ag_3 : Nominal.NPrf (.classEq F (synCoprab x y z
            (synWa (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))
              (.classEq (.cv z) R))))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A C) (.classMem B D) (.classMem S H))
        (.classEq (synCo A F B) S)) :=
  by
  have dv_cache_0001 : z ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
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
  have dv_cache_0004 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
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
  have dv_cache_0007 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0010 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_z, not_false_eq_true])
  have dv_cache_0011 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0012 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0013 : z ∉ (C).fv :=
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
        simp only [dv_C_z, not_false_eq_true])
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
  have dv_cache_0015 : y ∉ (D).fv :=
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
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0016 : z ∉ (D).fv :=
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
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.classEq S S)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_S_x,
          or_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((Wff.classEq S S)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_S_y,
          or_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((Wff.classEq S S)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_S_z,
          or_false, not_false_eq_true])
  have dv_cache_0020 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0021 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0022 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gEqid S
  have p0001 := @gSimp3 (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) S)
  have p0002 :=
    @gN3adant3 (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq R S)
      (.classEq (.cv z) S) hyp_ov2ag_1
  have p0003 :=
    @gEqeq12d (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) S))
      (.cv z) S R S p0001 p0002
  have p0004 := @gMoeq z R dv_cache_0001
  have p0005 :=
    @gA1i (synWmo z (.classEq (.cv z) R))
      (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0004
  have p0006 :=
    @gOvig (.classEq (.cv z) R) (.classEq S S) x y z A B S H C D F dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0003 p0005 hyp_ov2ag_3
  have p0007 :=
    @gMpi (synW3a (.classMem A C) (.classMem B D) (.classMem S H)) (.classEq S S)
      (.classEq (synCo A F B) S) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_oprabid2`. -/
@[expose]
noncomputable def gOprabid2 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq
        (synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)) A) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv u)).fv :=
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
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv u)).fv :=
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
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv u)).fv :=
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
          fresh_z_ne_u, not_false_eq_true])
  have dv_cache_0010 :
    x ∉ ((Wff.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_t, fresh_x_ne_u, dv_A_x,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉ ((Wff.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, fresh_y_ne_u, dv_A_y,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    z ∉ ((Wff.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, fresh_z_ne_u, dv_A_z,
          or_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0016 :
    w ∉
      ((synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coprab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, fresh_w_not_A,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coprab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_z, fresh_t_not_A,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    u ∉
      ((synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coprab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_ne_z, fresh_u_not_A,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0020 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0021 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0022 : w ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0023 : w ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0024 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have p0000 := @gVex w
  have p0001 := @gVex t
  have p0002 := @gVex u
  have p0003 := @gOpeq1 (.cv x) (.cv w) (.cv y)
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x w) (.classEq (synCop (.cv x) (.cv y)) (synCop (.cv w) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @gOpeq1d (.objEq x w) (synCop (.cv x) (.cv y)) (synCop (.cv w) (.cv y)) (.cv z)
      p0004_e00_recanon
  have p0005 :=
    @gEleq1d (.objEq x w) (synCop (synCop (.cv x) (.cv y)) (.cv z))
      (synCop (synCop (.cv w) (.cv y)) (.cv z)) A p0004
  have p0006 := @gOpeq2 (.cv y) (.cv t) (.cv w)
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y t) (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv w) (.cv t)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gOpeq1d (.objEq y t) (synCop (.cv w) (.cv y)) (synCop (.cv w) (.cv t)) (.cv z)
      p0007_e00_recanon
  have p0008 :=
    @gEleq1d (.objEq y t) (synCop (synCop (.cv w) (.cv y)) (.cv z))
      (synCop (synCop (.cv w) (.cv t)) (.cv z)) A p0007
  have p0009 := @gOpeq2 (.cv z) (.cv u) (synCop (.cv w) (.cv t))
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z u) (.classEq (synCop (synCop (.cv w) (.cv t)) (.cv z))
          (synCop (synCop (.cv w) (.cv t)) (.cv u)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gEleq1d (.objEq z u) (synCop (synCop (.cv w) (.cv t)) (.cv z))
      (synCop (synCop (.cv w) (.cv t)) (.cv u)) A p0010_e00_recanon
  have p0011_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w))
        (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
          (.classMem (synCop (synCop (.cv w) (.cv y)) (.cv z)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0011_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv t))
        (synWb (.classMem (synCop (synCop (.cv w) (.cv y)) (.cv z)) A)
          (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv z)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0011_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv u))
        (synWb (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv z)) A)
          (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @gEloprabg (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)
      (.classMem (synCop (synCop (.cv w) (.cv y)) (.cv z)) A)
      (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv z)) A)
      (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u)) A) x y z (.cv w) (.cv t)
      (.cv u) (synCvv) (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      p0011_e00_recanon p0011_e01_recanon p0011_e02_recanon
  have p0012 :=
    @gMp3an (.classMem (.cv w) (synCvv)) (.classMem (.cv t) (synCvv))
      (.classMem (.cv u) (synCvv))
      (synWb (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u))
          (synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)))
        (.classMem (synCop (synCop (.cv w) (.cv t)) (.cv u)) A))
      p0000 p0001 p0002 p0011
  have p0013 :=
    @gEqoprriv w t u
      (synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A)) A
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_oprabbi2i`. -/
@[expose]
noncomputable def gOprabbi2i (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_oprabbi2i_1 : Nominal.NPrf
        (synWb (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A) ph)) :
    Nominal.NPrf (.classEq A (synCoprab x y z ph)) :=
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
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @gOprabid2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gOprabbii (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A) ph x y z
      dv_cache_0005 dv_cache_0006 hyp_oprabbi2i_1
  have p0002 :=
    @gEqtr3i (synCoprab x y z (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv z)) A))
      A (synCoprab x y z ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elovex12`. -/
@[expose]
noncomputable def gElovex12 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCo B F C))
        (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))) :=
  by
  have p0000 := @gNe0i (synCo B F C) A
  have p0001 := @gOpexb B C
  have p0002 := (Nominal.classEqRefl (synCo B F C))
  have p0003 := @gFvprc (synCop B C) F
  have p0004 :=
    @gSyl5eq (.neg (.classMem (synCop B C) (synCvv))) (synCo B F C)
      (synCfv F (synCop B C)) (synC0) p0002 p0003
  have p0005 :=
    @gSylnbir (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classMem (synCop B C) (synCvv)) (.classEq (synCo B F C) (synC0)) p0001 p0004
  have p0006 :=
    @gNecon1ai (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) (synCo B F C)
      (synC0) p0005
  have p0007 :=
    @gSyl (.classMem A (synCo B F C)) (synWne (synCo B F C) (synC0))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_elovex1`. -/
@[expose]
noncomputable def gElovex1 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (synCo B F C)) (.classMem B (synCvv))) :=
  by
  have p0000 := @gElovex12 A B C F
  have p0001 :=
    @gSimpld (.classMem A (synCo B F C)) (.classMem B (synCvv)) (.classMem C (synCvv))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elovex2`. -/
@[expose]
noncomputable def gElovex2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (synCo B F C)) (.classMem C (synCvv))) :=
  by
  have p0000 := @gElovex12 A B C F
  have p0001 :=
    @gSimprd (.classMem A (synCo B F C)) (.classMem B (synCvv)) (.classMem C (synCvv))
      p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
