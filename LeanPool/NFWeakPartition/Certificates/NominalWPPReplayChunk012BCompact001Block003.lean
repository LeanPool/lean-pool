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

@[expose]
noncomputable def g_n_1st2nd2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cxp B C))
        (.classEq A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A)))) :=
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
    y ∉ ((Wff.classEq A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A)))).fv :=
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
    x ∉ ((Wff.classEq A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A)))).fv :=
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
    @g_elxp2 x y A B C dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_opfv1st (.cv x) (.cv y) p0001 p0002
  have p0004 := @g_opfv2nd (.cv x) (.cv y) p0001 p0002
  have p0005 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop (.cv x) (.cv y))) (.cv x)
      (syn_cfv (syn_c2nd) (syn_cop (.cv x) (.cv y))) (.cv y) p0003 p0004
  have p0006 :=
    @g_eqcomi
      (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv x) (.cv y)))
        (syn_cfv (syn_c2nd) (syn_cop (.cv x) (.cv y))))
      (syn_cop (.cv x) (.cv y)) p0005
  have p0007 := @g_id (.classEq A (syn_cop (.cv x) (.cv y)))
  have p0008 := @g_fveq2 A (syn_cop (.cv x) (.cv y)) (syn_c1st)
  have p0009 := @g_fveq2 A (syn_cop (.cv x) (.cv y)) (syn_c2nd)
  have p0010 :=
    @g_opeq12d (.classEq A (syn_cop (.cv x) (.cv y))) (syn_cfv (syn_c1st) A)
      (syn_cfv (syn_c1st) (syn_cop (.cv x) (.cv y))) (syn_cfv (syn_c2nd) A)
      (syn_cfv (syn_c2nd) (syn_cop (.cv x) (.cv y))) p0008 p0009
  have p0011 :=
    @g_n_3eqtr4a (.classEq A (syn_cop (.cv x) (.cv y))) (syn_cop (.cv x) (.cv y))
      (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv x) (.cv y)))
        (syn_cfv (syn_c2nd) (syn_cop (.cv x) (.cv y))))
      A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A)) p0006 p0007 p0010
  have p0012 :=
    @g_rexlimivw (.classEq A (syn_cop (.cv x) (.cv y)))
      (.classEq A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A))) y C
      dv_cache_0008 p0011
  have p0013 :=
    @g_rexlimivw (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y))))
      (.classEq A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A))) x B
      dv_cache_0009 p0012
  have p0014 :=
    @g_sylbi (.classMem A (syn_cxp B C))
      (syn_wrex x B (syn_wrex y C (.classEq A (syn_cop (.cv x) (.cv y)))))
      (.classEq A (syn_cop (syn_cfv (syn_c1st) A) (syn_cfv (syn_c2nd) A))) p0000 p0013
  exact p0014

@[expose]
noncomputable def g_fununiq (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun F) (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C)) :=
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
    x ∉ ((Wff.imp (syn_wa (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C))).fv :=
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
    y ∉ ((Wff.imp (syn_wa (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C))).fv :=
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
    z ∉ ((Wff.imp (syn_wa (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C))).fv :=
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
  have p0000 := @g_brex A B F
  have p0001 := @g_brex A C F
  have p0002 :=
    @g_anim12i (syn_wbr A F B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wbr A F C) (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))) p0000 p0001
  have p0003 :=
    @g_anandi (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0004 :=
    @g_sylibr (syn_wa (syn_wbr A F B) (syn_wbr A F C))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0002 p0003
  have p0005 :=
    @g_n_3adant1 (syn_wbr A F B) (syn_wbr A F C)
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      (syn_wfun F) p0004
  have p0006 :=
    @g_dffun2 x y z F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0007 := @g_breq12 (.cv x) A (.cv y) B F
  have p0008 :=
    @g_n_3adant3 (.classEq (.cv x) A) (.classEq (.cv y) B)
      (syn_wb (syn_wbr (.cv x) F (.cv y)) (syn_wbr A F B)) (.classEq (.cv z) C) p0007
  have p0009 := @g_breq12 (.cv x) A (.cv z) C F
  have p0010 :=
    @g_n_3adant2 (.classEq (.cv x) A) (.classEq (.cv z) C)
      (syn_wb (syn_wbr (.cv x) F (.cv z)) (syn_wbr A F C)) (.classEq (.cv y) B) p0009
  have p0011 :=
    @g_anbi12d (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      (syn_wbr (.cv x) F (.cv y)) (syn_wbr A F B) (syn_wbr (.cv x) F (.cv z))
      (syn_wbr A F C) p0008 p0010
  have p0012 := @g_eqeq12 (.cv y) B (.cv z) C
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (syn_wb (.objEq y z) (.classEq B C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
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
    @g_n_3adant1 (.classEq (.cv y) B) (.classEq (.cv z) C)
      (syn_wb (.objEq y z) (.classEq B C)) (.classEq (.cv x) A) p0013_e00_recanon
  have p0014 :=
    @g_imbi12d (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
      (syn_wa (syn_wbr A F B) (syn_wbr A F C)) (.objEq y z) (.classEq B C) p0011 p0013
  have p0015 :=
    @g_spc3gv
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C)) x y z A B C (syn_cvv)
      (syn_cvv) (syn_cvv) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0004 dv_cache_0005 dv_cache_0006 p0014
  have p0016 :=
    @g_syl5bi (syn_wfun F)
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
              (.objEq y z)))))
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.imp (syn_wa (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C)) p0006 p0015
  have p0017 :=
    @g_exp4a
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wfun F) (syn_wbr A F B) (syn_wbr A F C) (.classEq B C) p0016
  have p0018 :=
    @g_n_3impd
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wfun F) (syn_wbr A F B) (syn_wbr A F C) (.classEq B C) p0017
  have p0019 :=
    @g_n_3expb (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (.imp (syn_w3a (syn_wfun F) (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C)) p0018
  have p0020 :=
    @g_mpcom
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      (syn_w3a (syn_wfun F) (syn_wbr A F B) (syn_wbr A F C)) (.classEq B C) p0005 p0019
  exact p0020

@[expose]
noncomputable def g_cnvsi (R : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_csi R)) (syn_csi (syn_ccnv R))) :=
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
  have dv_cache_0008 : a ∉ ((syn_ccnv R)).fv :=
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
  have dv_cache_0009 : b ∉ ((syn_ccnv R)).fv :=
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
  have dv_cache_0011 : x ∉ ((syn_ccnv (syn_csi R))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_ccnv (syn_csi R))).fv :=
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
  have dv_cache_0013 : x ∉ ((syn_csi (syn_ccnv R))).fv :=
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
  have dv_cache_0014 : y ∉ ((syn_csi (syn_ccnv R))).fv :=
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
    @g_n_3ancoma (.classEq (.cv y) (syn_csn (.cv b))) (.classEq (.cv x) (syn_csn (.cv a)))
      (syn_wbr (.cv b) R (.cv a))
  have p0001 := @g_brcnv (.cv a) (.cv b) R
  have p0002 :=
    @g_n_3anbi3i (syn_wbr (.cv a) (syn_ccnv R) (.cv b)) (syn_wbr (.cv b) R (.cv a))
      (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) p0001
  have p0003 :=
    @g_bitr4i
      (syn_w3a (.classEq (.cv y) (syn_csn (.cv b))) (.classEq (.cv x) (syn_csn (.cv a)))
        (syn_wbr (.cv b) R (.cv a)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wbr (.cv b) R (.cv a)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wbr (.cv a) (syn_ccnv R) (.cv b)))
      p0000 p0002
  have p0004 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv y) (syn_csn (.cv b))) (.classEq (.cv x) (syn_csn (.cv a)))
        (syn_wbr (.cv b) R (.cv a)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wbr (.cv a) (syn_ccnv R) (.cv b)))
      a b p0003
  have p0005 := @g_brcnv (.cv x) (.cv y) (syn_csi R)
  have p0006 :=
    @g_brsi b a (.cv y) (.cv x) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_excom
      (syn_w3a (.classEq (.cv y) (syn_csn (.cv b))) (.classEq (.cv x) (syn_csn (.cv a)))
        (syn_wbr (.cv b) R (.cv a)))
      b a
  have p0008 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccnv (syn_csi R)) (.cv y))
      (syn_wbr (.cv y) (syn_csi R) (.cv x))
      (syn_wex b (syn_wex a (syn_w3a (.classEq (.cv y) (syn_csn (.cv b)))
            (.classEq (.cv x) (syn_csn (.cv a))) (syn_wbr (.cv b) R (.cv a)))))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv y) (syn_csn (.cv b)))
            (.classEq (.cv x) (syn_csn (.cv a))) (syn_wbr (.cv b) R (.cv a)))))
      p0005 p0006 p0007
  have p0009 :=
    @g_brsi a b (.cv x) (.cv y) (syn_ccnv R) dv_cache_0004 dv_cache_0003 dv_cache_0002
      dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0010 :=
    @g_n_3bitr4i
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv y) (syn_csn (.cv b)))
            (.classEq (.cv x) (syn_csn (.cv a))) (syn_wbr (.cv b) R (.cv a)))))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) (syn_ccnv R) (.cv b)))))
      (syn_wbr (.cv x) (syn_ccnv (syn_csi R)) (.cv y))
      (syn_wbr (.cv x) (syn_csi (syn_ccnv R)) (.cv y)) p0004 p0008 p0009
  have p0011 :=
    @g_eqbrriv x y (syn_ccnv (syn_csi R)) (syn_csi (syn_ccnv R)) dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0010
  exact p0011

@[expose]
noncomputable def g_dmsi (R : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_csi R)) (syn_cpw1 (syn_cdm R))) :=
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
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv := by
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
  have dv_cache_0002 : b ∉ ((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv :=
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
  have dv_cache_0003 : y ∉ ((syn_csn (.cv b))).fv :=
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
  have dv_cache_0004 : y ∉ ((syn_wbr (.cv a) R (.cv b))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_csi R)).fv :=
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
  have dv_cache_0015 : a ∉ ((syn_cdm R)).fv :=
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
  have dv_cache_0016 : x ∉ ((syn_cdm (syn_csi R))).fv :=
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
  have dv_cache_0017 : x ∉ ((syn_cpw1 (syn_cdm R))).fv :=
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
    @g_n_3anass (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
      (syn_wbr (.cv a) R (.cv b))
  have p0001 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wbr (.cv a) R (.cv b)))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a)))
        (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))
      y b p0000
  have p0002 :=
    @g_n_19_42vv (.classEq (.cv x) (syn_csn (.cv a)))
      (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))) y b
      dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_bitri
      (syn_wex y (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      (syn_wex y (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (.cv a)))
            (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (syn_wex y (syn_wex b
            (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      p0001 p0002
  have p0004 := @g_snex (.cv b)
  have p0005 := @g_isseti y (syn_csn (.cv b)) dv_cache_0003 p0004
  have p0006 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)) y
      dv_cache_0004
  have p0007 :=
    @g_mpbiran
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))
      (syn_wex y (.classEq (.cv y) (syn_csn (.cv b)))) (syn_wbr (.cv a) R (.cv b)) p0005
      p0006
  have p0008 :=
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))
      (syn_wbr (.cv a) R (.cv b)) b p0007
  have p0009 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))) y b
  have p0010 := @g_eldm b (.cv a) R dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_n_3bitr4i
      (syn_wex b (syn_wex y
          (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      (syn_wex b (syn_wbr (.cv a) R (.cv b)))
      (syn_wex y (syn_wex b
          (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      (.classMem (.cv a) (syn_cdm R)) p0008 p0009 p0010
  have p0012 :=
    @g_anbi2i
      (syn_wex y (syn_wex b
          (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      (.classMem (.cv a) (syn_cdm R)) (.classEq (.cv x) (syn_csn (.cv a))) p0011
  have p0013 :=
    @g_ancom (.classEq (.cv x) (syn_csn (.cv a))) (.classMem (.cv a) (syn_cdm R))
  have p0014 :=
    @g_bitri
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (syn_wex y (syn_wex b
            (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classMem (.cv a) (syn_cdm R)))
      (syn_wa (.classMem (.cv a) (syn_cdm R)) (.classEq (.cv x) (syn_csn (.cv a)))) p0012
      p0013
  have p0015 :=
    @g_bitri
      (syn_wex y (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (syn_wex y (syn_wex b
            (syn_wa (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      (syn_wa (.classMem (.cv a) (syn_cdm R)) (.classEq (.cv x) (syn_csn (.cv a)))) p0003
      p0014
  have p0016 :=
    @g_exbii
      (syn_wex y (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      (syn_wa (.classMem (.cv a) (syn_cdm R)) (.classEq (.cv x) (syn_csn (.cv a)))) a
      p0015
  have p0017 :=
    @g_excom
      (syn_wex b
        (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
          (syn_wbr (.cv a) R (.cv b))))
      y a
  have p0018 :=
    (Nominal.biimpRefl (syn_wrex a (syn_cdm R) (.classEq (.cv x) (syn_csn (.cv a)))))
  have p0019 :=
    @g_n_3bitr4i
      (syn_wex a (syn_wex y (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      (syn_wex a (syn_wa (.classMem (.cv a) (syn_cdm R)) (.classEq (.cv x) (syn_csn (.cv a)))))
      (syn_wex y (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      (syn_wrex a (syn_cdm R) (.classEq (.cv x) (syn_csn (.cv a)))) p0016 p0017 p0018
  have p0020 := @g_eldm y (.cv x) (syn_csi R) dv_cache_0007 dv_cache_0008
  have p0021 :=
    @g_brsi a b (.cv x) (.cv y) R dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0006 dv_cache_0014
  have p0022 :=
    @g_exbii (syn_wbr (.cv x) (syn_csi R) (.cv y))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b)))))
      y p0021
  have p0023 :=
    @g_bitri (.classMem (.cv x) (syn_cdm (syn_csi R)))
      (syn_wex y (syn_wbr (.cv x) (syn_csi R) (.cv y)))
      (syn_wex y (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      p0020 p0022
  have p0024 := @g_elpw1 a (.cv x) (syn_cdm R) dv_cache_0009 dv_cache_0015
  have p0025 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) R (.cv b))))))
      (syn_wrex a (syn_cdm R) (.classEq (.cv x) (syn_csn (.cv a))))
      (.classMem (.cv x) (syn_cdm (syn_csi R))) (.classMem (.cv x) (syn_cpw1 (syn_cdm R)))
      p0019 p0023 p0024
  have p0026 :=
    @g_eqriv x (syn_cdm (syn_csi R)) (syn_cpw1 (syn_cdm R)) dv_cache_0016 dv_cache_0017
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

@[expose]
noncomputable def g_funsi (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wfun (syn_csi F))) :=
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
      ((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
          (syn_wbr (.cv a) F (.cv b)))).fv :=
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
      ((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
          (syn_wbr (.cv a) F (.cv b)))).fv :=
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
      ((syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d)))).fv :=
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
      ((syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d)))).fv :=
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
  have dv_cache_0023 : c ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0024 : d ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0027 : a ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0028 : b ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0029 : z ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0030 : x ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0031 : y ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0032 : x ∉ ((syn_csi F)).fv :=
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
  have dv_cache_0033 : y ∉ ((syn_csi F)).fv :=
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
  have dv_cache_0034 : z ∉ ((syn_csi F)).fv :=
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
    @g_brsi a b (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_brsi c d (.cv x) (.cv z) F dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0002 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_csi F) (.cv y))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)))))
      (syn_wbr (.cv x) (syn_csi F) (.cv z))
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))))
      p0000 p0001
  have p0003 :=
    @g_ee4anv
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wbr (.cv a) F (.cv b)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
        (syn_wbr (.cv c) F (.cv d)))
      a b c d dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020
  have p0004 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z)))
      (syn_wa (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b))))) (syn_wex c
          (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
              (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))))))
      (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_wa
                (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
                  (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)))
                (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
                  (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))))))))
      p0002 p0003
  have p0005 := @g_fununiq (.cv a) (.cv b) (.cv d) F
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun F) (syn_wbr (.cv a) F (.cv b)) (syn_wbr (.cv a) F (.cv d)))
        (.objEq b d)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_wbr syn_cop syn_cun syn_wrex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0005
  have p0006 :=
    @g_n_3exp (syn_wfun F) (syn_wbr (.cv a) F (.cv b)) (syn_wbr (.cv a) F (.cv d))
      (.objEq b d) p0006_e00_recanon
  have p0007 := @g_breq1 (.cv a) (.cv c) (.cv d) F
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a c) (syn_wb (syn_wbr (.cv a) F (.cv d)) (syn_wbr (.cv c) F (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_bicomd (.objEq a c) (syn_wbr (.cv a) F (.cv d)) (syn_wbr (.cv c) F (.cv d))
      p0008_e00_recanon
  have p0009 :=
    @g_adantr (.objEq a c)
      (syn_wb (syn_wbr (.cv c) F (.cv d)) (syn_wbr (.cv a) F (.cv d)))
      (.classEq (.cv z) (syn_csn (.cv d))) p0008
  have p0010 := @g_eqeq2 (.cv z) (syn_csn (.cv d)) (syn_csn (.cv b))
  have p0011 := @g_vex b
  have p0012 := @g_sneqb (.cv b) (.cv d) p0011
  have p0013_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv b)) (syn_csn (.cv d))) (.objEq b d)) :=
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
      p0012
  have p0013 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))
      (.classEq (syn_csn (.cv b)) (syn_csn (.cv d))) (.objEq b d) p0010 p0013_e01_recanon
  have p0014 :=
    @g_adantl (.classEq (.cv z) (syn_csn (.cv d)))
      (syn_wb (.classEq (syn_csn (.cv b)) (.cv z)) (.objEq b d)) (.objEq a c) p0013
  have p0015 :=
    @g_imbi12d (syn_wa (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))))
      (syn_wbr (.cv c) F (.cv d)) (syn_wbr (.cv a) F (.cv d))
      (.classEq (syn_csn (.cv b)) (.cv z)) (.objEq b d) p0009 p0014
  have p0016 :=
    @g_biimprcd (syn_wa (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))))
      (.imp (syn_wbr (.cv c) F (.cv d)) (.classEq (syn_csn (.cv b)) (.cv z)))
      (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) p0015
  have p0017 :=
    @g_exp3a (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) (.objEq a c)
      (.classEq (.cv z) (syn_csn (.cv d)))
      (.imp (syn_wbr (.cv c) F (.cv d)) (.classEq (syn_csn (.cv b)) (.cv z))) p0016
  have p0018 :=
    @g_n_3impd (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d)) (.objEq a c)
      (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))
      (.classEq (syn_csn (.cv b)) (.cv z)) p0017
  have p0019 :=
    @g_syl6 (syn_wfun F) (syn_wbr (.cv a) F (.cv b))
      (.imp (syn_wbr (.cv a) F (.cv d)) (.objEq b d))
      (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)))
      p0006 p0018
  have p0020 := @g_eqeq1 (.cv x) (syn_csn (.cv a)) (syn_csn (.cv c))
  have p0021 := @g_vex a
  have p0022 := @g_sneqb (.cv a) (.cv c) p0021
  have p0023_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv a)) (syn_csn (.cv c))) (.objEq a c)) :=
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
      p0022
  have p0023 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv x) (syn_csn (.cv c)))
      (.classEq (syn_csn (.cv a)) (syn_csn (.cv c))) (.objEq a c) p0020 p0023_e01_recanon
  have p0024 :=
    @g_n_3anbi1d (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv x) (syn_csn (.cv c)))
      (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)) p0023
  have p0025 :=
    @g_adantr (.classEq (.cv x) (syn_csn (.cv a)))
      (syn_wb (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d)))
        (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))))
      (.classEq (.cv y) (syn_csn (.cv b))) p0024
  have p0026 := @g_eqeq1 (.cv y) (syn_csn (.cv b)) (.cv z)
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wb (.objEq y z) (.classEq (syn_csn (.cv b)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
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
    @g_adantl (.classEq (.cv y) (syn_csn (.cv b)))
      (syn_wb (.objEq y z) (.classEq (syn_csn (.cv b)) (.cv z)))
      (.classEq (.cv x) (syn_csn (.cv a))) p0027_e00_recanon
  have p0028 :=
    @g_imbi12d
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
        (syn_wbr (.cv c) F (.cv d)))
      (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d)))
      (.objEq y z) (.classEq (syn_csn (.cv b)) (.cv z)) p0025 p0027
  have p0029 :=
    @g_imbi2d
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d))) (.objEq y z))
      (.imp (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z)))
      (syn_wbr (.cv a) F (.cv b)) p0028
  have p0030 :=
    @g_biimprcd
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z)))
      (.imp (syn_wbr (.cv a) F (.cv b)) (.imp
          (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))
            (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))))
      p0029
  have p0031 :=
    @g_exp3a
      (.imp (syn_wbr (.cv a) F (.cv b)) (.imp
          (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))
            (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))))
      (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
      (.imp (syn_wbr (.cv a) F (.cv b)) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z)))
      p0030
  have p0032 :=
    @g_n_3impd
      (.imp (syn_wbr (.cv a) F (.cv b)) (.imp
          (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))
            (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))))
      (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
      (syn_wbr (.cv a) F (.cv b))
      (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d))) (.objEq y z))
      p0031
  have p0033 :=
    @g_syl (syn_wfun F)
      (.imp (syn_wbr (.cv a) F (.cv b)) (.imp
          (syn_w3a (.objEq a c) (.classEq (.cv z) (syn_csn (.cv d)))
            (syn_wbr (.cv c) F (.cv d))) (.classEq (syn_csn (.cv b)) (.cv z))))
      (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
          (syn_wbr (.cv a) F (.cv b))) (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))) (.objEq y z)))
      p0019 p0032
  have p0034 :=
    @g_imp3a (syn_wfun F)
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (syn_wbr (.cv a) F (.cv b)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
        (syn_wbr (.cv c) F (.cv d)))
      (.objEq y z) p0033
  have p0035 :=
    @g_exlimdvv (syn_wfun F)
      (syn_wa (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
          (syn_wbr (.cv a) F (.cv b)))
        (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv z) (syn_csn (.cv d)))
          (syn_wbr (.cv c) F (.cv d))))
      (.objEq y z) c d dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0034
  have p0036 :=
    @g_exlimdvv (syn_wfun F)
      (syn_wex c (syn_wex d (syn_wa (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)))
            (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
              (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))))))
      (.objEq y z) a b dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 p0035
  have p0037 :=
    @g_syl5bi
      (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z)))
      (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_wa
                (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
                  (.classEq (.cv y) (syn_csn (.cv b))) (syn_wbr (.cv a) F (.cv b)))
                (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
                  (.classEq (.cv z) (syn_csn (.cv d))) (syn_wbr (.cv c) F (.cv d))))))))
      (syn_wfun F) (.objEq y z) p0004 p0036
  have p0038 :=
    @g_alrimiv (syn_wfun F)
      (.imp (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y)) (syn_wbr (.cv x) (syn_csi F) (.cv z)))
        (.objEq y z))
      z dv_cache_0029 p0037
  have p0039 :=
    @g_alrimivv (syn_wfun F)
      (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y))
            (syn_wbr (.cv x) (syn_csi F) (.cv z))) (.objEq y z)))
      x y dv_cache_0030 dv_cache_0031 p0038
  have p0040 :=
    @g_dffun2 x y z (syn_csi F) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
  have p0041 :=
    @g_sylibr (syn_wfun F)
      (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_csi F) (.cv y))
                (syn_wbr (.cv x) (syn_csi F) (.cv z))) (.objEq y z)))))
      (syn_wfun (syn_csi F)) p0039 p0040
  exact p0041

@[expose]
noncomputable def g_rnsi (R : Class) :
    Nominal.NPrf (.classEq (syn_crn (syn_csi R)) (syn_cpw1 (syn_crn R))) :=
  by
  have p0000 := @g_cnvsi R
  have p0001 := @g_dmeqi (syn_ccnv (syn_csi R)) (syn_csi (syn_ccnv R)) p0000
  have p0002 := @g_dmsi (syn_ccnv R)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_ccnv (syn_csi R))) (syn_cdm (syn_csi (syn_ccnv R)))
      (syn_cpw1 (syn_cdm (syn_ccnv R))) p0001 p0002
  have p0004 := @g_dfrn4 (syn_csi R)
  have p0005 := @g_dfrn4 R
  have p0006 := @g_pw1eq (syn_crn R) (syn_cdm (syn_ccnv R))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cdm (syn_ccnv (syn_csi R))) (syn_cpw1 (syn_cdm (syn_ccnv R)))
      (syn_crn (syn_csi R)) (syn_cpw1 (syn_crn R)) p0003 p0004 p0007
  exact p0008

@[expose]
noncomputable def g_op1std (A : Class) (B : Class) (C : Class)
    (hyp_op1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_op1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq C (syn_cop A B)) (.classEq (syn_cfv (syn_c1st) C) A)) :=
  by
  have p0000 := @g_fveq2 C (syn_cop A B) (syn_c1st)
  have p0001 := @g_opfv1st A B hyp_op1st_1 hyp_op1st_2
  have p0002 :=
    @g_syl6eq (.classEq C (syn_cop A B)) (syn_cfv (syn_c1st) C)
      (syn_cfv (syn_c1st) (syn_cop A B)) A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_op2ndd (A : Class) (B : Class) (C : Class)
    (hyp_op1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_op1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq C (syn_cop A B)) (.classEq (syn_cfv (syn_c2nd) C) B)) :=
  by
  have p0000 := @g_fveq2 C (syn_cop A B) (syn_c2nd)
  have p0001 := @g_opfv2nd A B hyp_op1st_1 hyp_op1st_2
  have p0002 :=
    @g_syl6eq (.classEq C (syn_cop A B)) (syn_cfv (syn_c2nd) C)
      (syn_cfv (syn_c2nd) (syn_cop A B)) B p0000 p0001
  exact p0002

@[expose]
noncomputable def g_oveq1 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_co A F C) (syn_co B F C))) :=
  by
  have p0000 := @g_opeq1 A B C
  have p0001 := @g_fveq2d (.classEq A B) (syn_cop A C) (syn_cop B C) F p0000
  have p0002 := (Nominal.classEqRefl (syn_co A F C))
  have p0003 := (Nominal.classEqRefl (syn_co B F C))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cfv F (syn_cop A C)) (syn_cfv F (syn_cop B C))
      (syn_co A F C) (syn_co B F C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_oveq2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_co C F A) (syn_co C F B))) :=
  by
  have p0000 := @g_opeq2 A B C
  have p0001 := @g_fveq2d (.classEq A B) (syn_cop C A) (syn_cop C B) F p0000
  have p0002 := (Nominal.classEqRefl (syn_co C F A))
  have p0003 := (Nominal.classEqRefl (syn_co C F B))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cfv F (syn_cop C A)) (syn_cfv F (syn_cop C B))
      (syn_co C F A) (syn_co C F B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_oveq12 (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_co A F C) (syn_co B F D))) :=
  by
  have p0000 := @g_oveq1 A B C F
  have p0001 := @g_oveq2 C D B F
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_co A F C) (syn_co B F C) (syn_co B F D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_oveq2d (ph : Wff) (A : Class) (B : Class) (C : Class) (F : Class)
    (hyp_oveq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_co C F A) (syn_co C F B))) :=
  by
  have p0000 := @g_oveq2 A B C F
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_co C F A) (syn_co C F B)) hyp_oveq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_ovex (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.classMem (syn_co A F B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_co A F B))
  have p0001 := @g_fvex (syn_cop A B) F
  have p0002 := @g_eqeltri (syn_co A F B) (syn_cfv F (syn_cop A B)) (syn_cvv) p0000 p0001
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

@[expose]
noncomputable def g_dfoprab2 (ph : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_coprab x y z ph) (syn_copab w z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) :=
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
  have dv_cache_0001 : w ∉ ((syn_cop (.cv x) (.cv y))).fv := by
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
    w ∉ ((syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv v) (syn_cop (.cv w) (.cv z)))).fv :=
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
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv v) (syn_cop (.cv w) (.cv z)))).fv :=
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
      ((syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))).fv :=
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
    @g_excom
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
            (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      z w
  have p0001 :=
    @g_exrot4
      (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
        (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))
      z w x y
  have p0002 :=
    @g_an12 (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
      (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph
  have p0003 :=
    @g_exbii
      (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
        (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) ph))
      w p0002
  have p0004 := @g_vex x
  have p0005 := @g_vex y
  have p0006 := @g_opex (.cv x) (.cv y) p0004 p0005
  have p0007 := @g_opeq1 (.cv w) (syn_cop (.cv x) (.cv y)) (.cv z)
  have p0008 :=
    @g_eqeq2d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv w) (.cv z))
      (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) (.cv v) p0007
  have p0009 :=
    @g_anbi1d (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
      (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
      (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph p0008
  have p0010 :=
    @g_ceqsexv (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) ph)
      (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) w
      (syn_cop (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002 p0006 p0009
  have p0011 :=
    @g_bitri
      (syn_wex w (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
          (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) ph)))
      (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) p0003
      p0010
  have p0012 :=
    @g_n_3exbii
      (syn_wex w (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
          (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) x y z
      p0011
  have p0013 :=
    @g_bitri
      (syn_wex z (syn_wex w (syn_wex x (syn_wex y
              (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
                (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))
      (syn_wex x (syn_wex y (syn_wex z (syn_wex w
              (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
                (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      p0001 p0012
  have p0014 :=
    @g_n_19_42vv (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) x y dv_cache_0003
      dv_cache_0004
  have p0015 :=
    @g_n_2exbii
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
            (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      w z p0014
  have p0016 :=
    @g_n_3bitr3i
      (syn_wex z (syn_wex w (syn_wex x (syn_wex y
              (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
                (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))
      (syn_wex w (syn_wex z (syn_wex x (syn_wex y
              (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
                (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      (syn_wex w (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wex x
              (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))
      p0000 p0013 p0015
  have p0017 :=
    @g_abbii
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      (syn_wex w (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z))) (syn_wex x
              (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))))
      v p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ph x y z v
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) w z
      v dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0020 :=
    @g_n_3eqtr4i
      (.cab v (syn_wex x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv v) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))))
      (.cab v (syn_wex w (syn_wex z (syn_wa (.classEq (.cv v) (syn_cop (.cv w) (.cv z)))
              (syn_wex x
                (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))))
      (syn_coprab x y z ph)
      (syn_copab w z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      p0017 p0018 p0019
  exact p0020

@[expose]
noncomputable def g_oprabbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (_dv_x_z : x ≠ z) (_dv_y_z : y ≠ z)
    (hyp_oprabbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_oprabbid_2 : Nominal.NPrf (syn_wnf y ph))
    (hyp_oprabbid_3 : Nominal.NPrf (syn_wnf z ph))
    (hyp_oprabbid_4 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_coprab x y z ps) (syn_coprab x y z ch))) :=
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
    @g_anbi2d ph ps ch (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)))
      hyp_oprabbid_4
  have p0001 :=
    @g_exbid ph (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps)
      (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch) z
      hyp_oprabbid_3 p0000
  have p0002 :=
    @g_exbid ph
      (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps))
      (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch))
      y hyp_oprabbid_2 p0001
  have p0003 :=
    @g_exbid ph
      (syn_wex y (syn_wex z
          (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps)))
      (syn_wex y (syn_wex z
          (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch)))
      x hyp_oprabbid_1 p0002
  have p0004 :=
    @g_abbidv ph
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps))))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch))))
      w dv_cache_0001 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ps x y z w
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ch x y z w
      dv_cache_0006 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_n_3eqtr4g ph
      (.cab w (syn_wex x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ps)))))
      (.cab w (syn_wex x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ch)))))
      (syn_coprab x y z ps) (syn_coprab x y z ch) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_oprabbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_oprabbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_coprab x y z ps) (syn_coprab x y z ch))) :=
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
  have p0000 := @g_nfv ph x dv_cache_0001
  have p0001 := @g_nfv ph y dv_cache_0002
  have p0002 := @g_nfv ph z dv_cache_0003
  have p0003 :=
    @g_oprabbid ph ps ch x y z dv_cache_0004 dv_cache_0005 p0000 p0001 p0002
      hyp_oprabbidv_1
  exact p0003

@[expose]
noncomputable def g_oprabbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_oprabbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (.classEq (syn_coprab x y z ph) (syn_coprab x y z ps)) :=
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
  have p0000 := @g_eqid (.cv w)
  have p0001 := @g_a1i (syn_wb ph ps) (.classEq (.cv w) (.cv w)) hyp_oprabbii_1
  have p0002 :=
    @g_oprabbidv (.classEq (.cv w) (.cv w)) ph ps x y z dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0001
  have p0003 := Nominal.mp p0000 p0002
  exact p0003

@[expose]
noncomputable def g_cbvoprab12 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (w : Var) (v : Var) (dv_v_w : v ≠ w) (dv_v_x : v ≠ x) (dv_v_y : v ≠ y)
    (dv_v_z : v ≠ z) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_cbvoprab12_1 : Nominal.NPrf (syn_wnf w ph))
    (hyp_cbvoprab12_2 : Nominal.NPrf (syn_wnf v ph))
    (hyp_cbvoprab12_3 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvoprab12_4 : Nominal.NPrf (syn_wnf y ps))
    (hyp_cbvoprab12_5 : Nominal.NPrf (.imp (syn_wa (.objEq x w) (.objEq y v)) (syn_wb ph ps))) :
    Nominal.NPrf (.classEq (syn_coprab x y z ph) (syn_coprab w v z ps)) :=
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
  have dv_cache_0001 : w ∉ ((Wff.classEq (.cv u) (syn_cop (.cv x) (.cv y)))).fv := by
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
  have dv_cache_0002 : v ∉ ((Wff.classEq (.cv u) (syn_cop (.cv x) (.cv y)))).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv u) (syn_cop (.cv w) (.cv v)))).fv :=
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
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv u) (syn_cop (.cv w) (.cv v)))).fv :=
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
  have p0000 := @g_nfv (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) w dv_cache_0001
  have p0001 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph w p0000 hyp_cbvoprab12_1
  have p0002 := @g_nfv (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) v dv_cache_0002
  have p0003 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph v p0002 hyp_cbvoprab12_2
  have p0004 := @g_nfv (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) x dv_cache_0003
  have p0005 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps x p0004 hyp_cbvoprab12_3
  have p0006 := @g_nfv (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) y dv_cache_0004
  have p0007 :=
    @g_nfan (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps y p0006 hyp_cbvoprab12_4
  have p0008 := @g_opeq12 (.cv x) (.cv w) (.cv y) (.cv v)
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq x w) (.objEq y v))
        (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex
          syn_cphi
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
    @g_eqeq2d (syn_wa (.objEq x w) (.objEq y v)) (syn_cop (.cv x) (.cv y))
      (syn_cop (.cv w) (.cv v)) (.cv u) p0009_e00_recanon
  have p0010 :=
    @g_anbi12d (syn_wa (.objEq x w) (.objEq y v))
      (.classEq (.cv u) (syn_cop (.cv x) (.cv y)))
      (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ph ps p0009 hyp_cbvoprab12_5
  have p0011 :=
    @g_cbvex2 (syn_wa (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps) x y w v dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 p0001 p0003 p0005 p0007 p0010
  have p0012 :=
    @g_opabbii
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex w (syn_wex v (syn_wa (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps))) u z
      p0011
  have p0013 :=
    @g_dfoprab2 ph x y z u dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014
  have p0014 :=
    @g_dfoprab2 ps w v z u dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0012
      dv_cache_0018 dv_cache_0019
  have p0015 :=
    @g_n_3eqtr4i
      (syn_copab u z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv u) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_copab u z
        (syn_wex w (syn_wex v (syn_wa (.classEq (.cv u) (syn_cop (.cv w) (.cv v))) ps))))
      (syn_coprab x y z ph) (syn_coprab w v z ps) p0012 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_dmoprab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cdm (syn_coprab x y z ph)) (syn_copab x y (syn_wex z ph))) :=
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
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv w) (syn_cop (.cv x) (.cv y)))).fv :=
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
  have dv_cache_0008 : w ∉ ((syn_wex z ph)).fv :=
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
    @g_dfoprab2 ph x y z w dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_dmeqi (syn_coprab x y z ph)
      (syn_copab w z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      p0000
  have p0002 :=
    @g_dmopab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) w z
      dv_cache_0004
  have p0003 := @g_exrot3 (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) z x y
  have p0004 :=
    @g_n_19_42v (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph z dv_cache_0007
  have p0005 :=
    @g_n_2exbii (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph)) x y p0004
  have p0006 :=
    @g_bitri
      (syn_wex z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_wex x
        (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_wex x
        (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph))))
      p0003 p0005
  have p0007 :=
    @g_abbii
      (syn_wex z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_wex x
        (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph))))
      w p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab (syn_wex z ph)
      x y w dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0009 :=
    @g_eqtr4i
      (.cab w (syn_wex z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))
      (.cab w (syn_wex x (syn_wex y
            (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_wex z ph)))))
      (syn_copab x y (syn_wex z ph)) p0007 p0008
  have p0010 :=
    @g_n_3eqtri (syn_cdm (syn_coprab x y z ph))
      (syn_cdm (syn_copab w z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))
      (.cab w (syn_wex z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))
      (syn_copab x y (syn_wex z ph)) p0001 p0002 p0009
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

@[expose]
noncomputable def g_eloprabga (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_eloprabga_1 : Nominal.NPrf
        (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
        (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps)) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv w) (syn_cop (syn_cop A B) C))).fv := by
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
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv w) (syn_cop (syn_cop A B) C))).fv :=
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
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv w) (syn_cop (syn_cop A B) C))).fv :=
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
  have dv_cache_0022 : w ∉ ((syn_cop (syn_cop A B) C)).fv :=
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
      ((Wff.imp (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
            (.classMem C (syn_cvv)))
          (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps))).fv :=
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
  have p0000 := @g_elex A V
  have p0001 := @g_elex B W
  have p0002 := @g_elex C X
  have p0003 := @g_opexg A B (syn_cvv) (syn_cvv)
  have p0004 := @g_opexg (syn_cop A B) C (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_sylan (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_cop A B) (syn_cvv)) (.classMem C (syn_cvv))
      (.classMem (syn_cop (syn_cop A B) C) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_n_3impa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (.classMem (syn_cop (syn_cop A B) C) (syn_cvv)) p0005
  have p0007 :=
    @g_eqeq1 (.cv w) (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))
  have p0008 :=
    @g_eqcom (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))
  have p0009 := @g_opth (.cv x) (.cv y) A B
  have p0010 :=
    @g_anbi1i (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (.cv z) C) p0009
  have p0011 := @g_opth (syn_cop (.cv x) (.cv y)) (.cv z) (syn_cop A B) C
  have p0012 :=
    (Nominal.biimpRefl (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))
  have p0013 :=
    @g_n_3bitr4i
      (syn_wa (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (.classEq (.cv z) C))
      (syn_wa (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (.cv z) C))
      (.classEq (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) (syn_cop (syn_cop A B) C))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0010 p0011
      p0012
  have p0014 :=
    @g_bitri
      (.classEq (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)))
      (.classEq (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) (syn_cop (syn_cop A B) C))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0008 p0013
  have p0015 :=
    @g_syl6bb (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)))
      (.classEq (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0007 p0014
  have p0016 :=
    @g_anbi1d (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph p0015
  have p0017 :=
    @g_pm5_32i (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph
      ps hyp_eloprabga_1
  have p0018 :=
    @g_syl6bb (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)
      (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph)
      (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)
      p0016 p0017
  have p0019 :=
    @g_n_3exbidv (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)
      (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)
      x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 p0018
  have p0020 :=
    @g_adantl (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (syn_wb (syn_wex x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
        (syn_wex x (syn_wex y (syn_wex z (syn_wa
                (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)))))
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      p0019
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ph x y z w
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0022 :=
    @g_eleq2i (syn_coprab x y z ph)
      (.cab w (syn_wex x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))))
      (.cv w) p0021
  have p0023 :=
    @g_abid
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      w
  have p0024 :=
    @g_bitr2i (.classMem (.cv w) (syn_coprab x y z ph))
      (.classMem (.cv w) (.cab w (syn_wex x (syn_wex y (syn_wex z
                (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      p0022 p0023
  have p0025 := @g_eleq1 (.cv w) (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)
  have p0026 :=
    @g_syl5bb
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      (.classMem (.cv w) (syn_coprab x y z ph))
      (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) p0024 p0025
  have p0027 :=
    @g_adantl (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (syn_wb (syn_wex x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
        (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)))
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      p0026
  have p0028 := @g_isset x A dv_cache_0008
  have p0029 := @g_isset y B dv_cache_0009
  have p0030 := @g_isset z C dv_cache_0010
  have p0031 :=
    @g_n_3anbi123i (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A))
      (.classMem B (syn_cvv)) (syn_wex y (.classEq (.cv y) B)) (.classMem C (syn_cvv))
      (syn_wex z (.classEq (.cv z) C)) p0028 p0029 p0030
  have p0032 :=
    @g_eeeanv (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C) x y z
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018
  have p0033 :=
    @g_bitr4i
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_w3a (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B))
        (syn_wex z (.classEq (.cv z) C)))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      p0031 p0032
  have p0034 :=
    @g_biimpi
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      p0033
  have p0035 :=
    @g_biantrurd
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)))))
      ps p0034
  have p0036 :=
    @g_n_19_41vvv (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      ps x y z dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0037 :=
    @g_syl6rbbr
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) ps
      (syn_wa (syn_wex x (syn_wex y (syn_wex z
              (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))) ps)
      (syn_wex x (syn_wex y (syn_wex z (syn_wa
              (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))
      p0035 p0036
  have p0038 :=
    @g_adantr
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wa
                (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))
        ps)
      (.classEq (.cv w) (syn_cop (syn_cop A B) C)) p0037
  have p0039 :=
    @g_n_3bitr3d
      (syn_wa (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (.classEq (.cv w) (syn_cop (syn_cop A B) C)))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))
      (syn_wex x (syn_wex y (syn_wex z (syn_wa
              (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))
      (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps p0020 p0027 p0038
  have p0040 :=
    @g_expcom
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classEq (.cv w) (syn_cop (syn_cop A B) C))
      (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps) p0039
  have p0041 :=
    @g_vtocleg
      (.imp (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps))
      w (syn_cop (syn_cop A B) C) (syn_cvv) dv_cache_0022 dv_cache_0023 p0040
  have p0042 :=
    @g_mpcom (.classMem (syn_cop (syn_cop A B) C) (syn_cvv))
      (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps) p0006 p0041
  have p0043 :=
    @g_syl3an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B W)
      (.classMem B (syn_cvv)) (.classMem C X) (.classMem C (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps) p0000 p0001
      p0002 p0042
  exact p0043

@[expose]
noncomputable def g_eloprabg (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var)
    (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class)
    (X : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_th_x : x ∉ th.fv) (dv_th_y : y ∉ th.fv)
    (dv_th_z : z ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_eloprabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_eloprabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_eloprabg_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (syn_wb ch th))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
        (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) th)) :=
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
    @g_syl3an9b (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch (.classEq (.cv z) C) th
      hyp_eloprabg_1 hyp_eloprabg_2 hyp_eloprabg_3
  have p0001 :=
    @g_eloprabga ph th x y z A B C V W X dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      p0000
  exact p0001

@[expose]
noncomputable def g_funoprabg (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.all x (.all y (syn_wmo z ph))) (syn_wfun (syn_coprab x y z ph))) :=
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
  have dv_cache_0007 : w ∉ ((Wff.all x (.all y (syn_wmo z ph)))).fv :=
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
    @g_mosubopt ph z x y (.cv w) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_alrimiv (.all x (.all y (syn_wmo z ph)))
      (syn_wmo z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      w dv_cache_0007 p0000
  have p0002 :=
    @g_dfoprab2 ph x y z w dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
  have p0003 :=
    @g_funeqi (syn_coprab x y z ph)
      (syn_copab w z
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      p0002
  have p0004 :=
    @g_funopab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) w z
      dv_cache_0011
  have p0005 :=
    @g_bitr2i (syn_wfun (syn_coprab x y z ph))
      (syn_wfun (syn_copab w z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))
      (.all w (syn_wmo z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))
      p0003 p0004
  have p0006 :=
    @g_sylib (.all x (.all y (syn_wmo z ph)))
      (.all w (syn_wmo z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))))
      (syn_wfun (syn_coprab x y z ph)) p0001 p0005
  exact p0006

@[expose]
noncomputable def g_funoprab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_funoprab_1 : Nominal.NPrf (syn_wmo z ph)) :
    Nominal.NPrf (syn_wfun (syn_coprab x y z ph)) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @g_gen2 (syn_wmo z ph) x y hyp_funoprab_1
  have p0001 := @g_funoprabg ph x y z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fnoprabg (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.all x (.all y (.imp ph (syn_weu z ps))))
        (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph))) :=
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
  have p0000 := @g_eumo ps z
  have p0001 := @g_imim2i (syn_weu z ps) (syn_wmo z ps) ph p0000
  have p0002 := @g_moanimv ph ps z dv_cache_0001
  have p0003 :=
    @g_sylibr (.imp ph (syn_weu z ps)) (.imp ph (syn_wmo z ps)) (syn_wmo z (syn_wa ph ps))
      p0001 p0002
  have p0004 := @g_n_2alimi (.imp ph (syn_weu z ps)) (syn_wmo z (syn_wa ph ps)) x y p0003
  have p0005 :=
    @g_funoprabg (syn_wa ph ps) x y z dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_syl (.all x (.all y (.imp ph (syn_weu z ps))))
      (.all x (.all y (syn_wmo z (syn_wa ph ps))))
      (syn_wfun (syn_coprab x y z (syn_wa ph ps))) p0004 p0005
  have p0007 := @g_dmoprab (syn_wa ph ps) x y z dv_cache_0003 dv_cache_0004
  have p0008 := @g_nfa1 (.all y (.imp ph (syn_weu z ps))) x
  have p0009 := @g_nfa2 (.imp ph (syn_weu z ps)) y x
  have p0010 := @g_simpl ph ps
  have p0011 := @g_exlimiv (syn_wa ph ps) ph z dv_cache_0001 p0010
  have p0012 := @g_euex ps z
  have p0013 := @g_imim2i (syn_weu z ps) (syn_wex z ps) ph p0012
  have p0014 := @g_ancld (.imp ph (syn_weu z ps)) ph (syn_wex z ps) p0013
  have p0015 := @g_n_19_42v ph ps z dv_cache_0001
  have p0016 :=
    @g_syl6ibr (.imp ph (syn_weu z ps)) ph (syn_wa ph (syn_wex z ps))
      (syn_wex z (syn_wa ph ps)) p0014 p0015
  have p0017 :=
    @g_impbid2 (.imp ph (syn_weu z ps)) (syn_wex z (syn_wa ph ps)) ph p0011 p0016
  have p0018 :=
    @g_sps (.imp ph (syn_weu z ps)) (syn_wb (syn_wex z (syn_wa ph ps)) ph) y p0017
  have p0019 :=
    @g_sps (.all y (.imp ph (syn_weu z ps))) (syn_wb (syn_wex z (syn_wa ph ps)) ph) x
      p0018
  have p0020 :=
    @g_opabbid (.all x (.all y (.imp ph (syn_weu z ps)))) (syn_wex z (syn_wa ph ps)) ph x
      y p0008 p0009 p0019
  have p0021 :=
    @g_syl5eq (.all x (.all y (.imp ph (syn_weu z ps))))
      (syn_cdm (syn_coprab x y z (syn_wa ph ps)))
      (syn_copab x y (syn_wex z (syn_wa ph ps))) (syn_copab x y ph) p0007 p0020
  have p0022 :=
    (Nominal.biimpRefl (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph)))
  have p0023 :=
    @g_sylanbrc (.all x (.all y (.imp ph (syn_weu z ps))))
      (syn_wfun (syn_coprab x y z (syn_wa ph ps)))
      (.classEq (syn_cdm (syn_coprab x y z (syn_wa ph ps))) (syn_copab x y ph))
      (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph)) p0006 p0021 p0022
  exact p0023

@[expose]
noncomputable def g_fnoprab (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_fnoprab_1 : Nominal.NPrf (.imp ph (syn_weu z ps))) :
    Nominal.NPrf (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph)) :=
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
  have p0000 := @g_gen2 (.imp ph (syn_weu z ps)) x y hyp_fnoprab_1
  have p0001 :=
    @g_fnoprabg ph ps x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ovigg (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (F : Class) (V : Class) (W : Class) (X : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_ovigg_1 : Nominal.NPrf
        (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (syn_wb ph ps)))
    (hyp_ovigg_4 : Nominal.NPrf (syn_wmo z ph))
    (hyp_ovigg_5 : Nominal.NPrf (.classEq F (syn_coprab x y z ph))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
        (.imp ps (.classEq (syn_co A F B) C))) :=
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
    @g_eloprabga ph ps x y z A B C V W X dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      hyp_ovigg_1
  have p0001 := @g_funoprab ph x y z dv_cache_0013 dv_cache_0014 dv_cache_0015 hyp_ovigg_4
  have p0002 := @g_funopfv (syn_cop A B) C (syn_coprab x y z ph)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl6bir (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) ps
      (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph))
      (.classEq (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) C) p0000 p0003
  have p0005 := (Nominal.classEqRefl (syn_co A F B))
  have p0006 := @g_fveq1i (syn_cop A B) F (syn_coprab x y z ph) hyp_ovigg_5
  have p0007 :=
    @g_eqtri (syn_co A F B) (syn_cfv F (syn_cop A B))
      (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) p0005 p0006
  have p0008 :=
    @g_eqeq1i (syn_co A F B) (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) C p0007
  have p0009 :=
    @g_syl6ibr (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) ps
      (.classEq (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) C)
      (.classEq (syn_co A F B) C) p0004 p0008
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

@[expose]
noncomputable def g_ovig (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_ovig_1 : Nominal.NPrf
        (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
          (syn_wb ph ps)))
    (hyp_ovig_2 : Nominal.NPrf
        (.imp (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S)) (syn_wmo z ph)))
    (hyp_ovig_3 : Nominal.NPrf (.classEq F (syn_coprab x y z
            (syn_wa (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph)))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A R) (.classMem B S) (.classMem C D))
        (.imp ps (.classEq (syn_co A F B) C))) :=
  by
  have dv_cache_0001 : z ∉ ((syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S))).fv := by
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
  have dv_cache_0011 : x ∉ ((syn_wa (syn_wa (.classMem A R) (.classMem B S)) ps)).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_wa (syn_wa (.classMem A R) (.classMem B S)) ps)).fv :=
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
  have dv_cache_0013 : z ∉ ((syn_wa (syn_wa (.classMem A R) (.classMem B S)) ps)).fv :=
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
  have p0000 := @g_n_3simpa (.classMem A R) (.classMem B S) (.classMem C D)
  have p0001 := @g_eleq1 (.cv x) A R
  have p0002 := @g_eleq1 (.cv y) B S
  have p0003 :=
    @g_bi2anan9 (.classEq (.cv x) A) (.classMem (.cv x) R) (.classMem A R)
      (.classEq (.cv y) B) (.classMem (.cv y) S) (.classMem B S) p0001 p0002
  have p0004 :=
    @g_n_3adant3 (.classEq (.cv x) A) (.classEq (.cv y) B)
      (syn_wb (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S))
        (syn_wa (.classMem A R) (.classMem B S)))
      (.classEq (.cv z) C) p0003
  have p0005 :=
    @g_anbi12d (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))
      (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S))
      (syn_wa (.classMem A R) (.classMem B S)) ph ps p0004 hyp_ovig_1
  have p0006 :=
    @g_moanimv (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph z dv_cache_0001
  have p0007 :=
    @g_mpbir (syn_wmo z (syn_wa (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph))
      (.imp (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S)) (syn_wmo z ph))
      hyp_ovig_2 p0006
  have p0008 :=
    @g_ovigg (syn_wa (syn_wa (.classMem (.cv x) R) (.classMem (.cv y) S)) ph)
      (syn_wa (syn_wa (.classMem A R) (.classMem B S)) ps) x y z A B C F R S D
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 p0005 p0007 hyp_ovig_3
  have p0009 :=
    @g_mpand (syn_w3a (.classMem A R) (.classMem B S) (.classMem C D))
      (syn_wa (.classMem A R) (.classMem B S)) ps (.classEq (syn_co A F B) C) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_ov2ag (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (R : Class) (S : Class) (F : Class) (H : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_C_z : z ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (dv_R_z : z ∉ R.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_ov2ag_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq R S)))
    (hyp_ov2ag_3 : Nominal.NPrf (.classEq F (syn_coprab x y z
            (syn_wa (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))
              (.classEq (.cv z) R))))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A C) (.classMem B D) (.classMem S H))
        (.classEq (syn_co A F B) S)) :=
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
  have p0000 := @g_eqid S
  have p0001 := @g_simp3 (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) S)
  have p0002 :=
    @g_n_3adant3 (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq R S)
      (.classEq (.cv z) S) hyp_ov2ag_1
  have p0003 :=
    @g_eqeq12d (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) S))
      (.cv z) S R S p0001 p0002
  have p0004 := @g_moeq z R dv_cache_0001
  have p0005 :=
    @g_a1i (syn_wmo z (.classEq (.cv z) R))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0004
  have p0006 :=
    @g_ovig (.classEq (.cv z) R) (.classEq S S) x y z A B S H C D F dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0003 p0005 hyp_ov2ag_3
  have p0007 :=
    @g_mpi (syn_w3a (.classMem A C) (.classMem B D) (.classMem S H)) (.classEq S S)
      (.classEq (syn_co A F B) S) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_oprabid2 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq
        (syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)) A) :=
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
    x ∉ ((Wff.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A)).fv :=
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
    y ∉ ((Wff.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A)).fv :=
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
    z ∉ ((Wff.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A)).fv :=
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
      ((syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))).fv :=
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
      ((syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))).fv :=
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
      ((syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))).fv :=
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
  have p0000 := @g_vex w
  have p0001 := @g_vex t
  have p0002 := @g_vex u
  have p0003 := @g_opeq1 (.cv x) (.cv w) (.cv y)
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x w) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (.cv w) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_opeq1d (.objEq x w) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv w) (.cv y)) (.cv z)
      p0004_e00_recanon
  have p0005 :=
    @g_eleq1d (.objEq x w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))
      (syn_cop (syn_cop (.cv w) (.cv y)) (.cv z)) A p0004
  have p0006 := @g_opeq2 (.cv y) (.cv t) (.cv w)
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y t) (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv w) (.cv t)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_opeq1d (.objEq y t) (syn_cop (.cv w) (.cv y)) (syn_cop (.cv w) (.cv t)) (.cv z)
      p0007_e00_recanon
  have p0008 :=
    @g_eleq1d (.objEq y t) (syn_cop (syn_cop (.cv w) (.cv y)) (.cv z))
      (syn_cop (syn_cop (.cv w) (.cv t)) (.cv z)) A p0007
  have p0009 := @g_opeq2 (.cv z) (.cv u) (syn_cop (.cv w) (.cv t))
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z u) (.classEq (syn_cop (syn_cop (.cv w) (.cv t)) (.cv z))
          (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_eleq1d (.objEq z u) (syn_cop (syn_cop (.cv w) (.cv t)) (.cv z))
      (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A p0010_e00_recanon
  have p0011_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w))
        (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
          (.classMem (syn_cop (syn_cop (.cv w) (.cv y)) (.cv z)) A))) :=
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
  have p0011_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv t))
        (syn_wb (.classMem (syn_cop (syn_cop (.cv w) (.cv y)) (.cv z)) A)
          (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv z)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0011_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv u))
        (syn_wb (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv z)) A)
          (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @g_eloprabg (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)
      (.classMem (syn_cop (syn_cop (.cv w) (.cv y)) (.cv z)) A)
      (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv z)) A)
      (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A) x y z (.cv w) (.cv t)
      (.cv u) (syn_cvv) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      p0011_e00_recanon p0011_e01_recanon p0011_e02_recanon
  have p0012 :=
    @g_mp3an (.classMem (.cv w) (syn_cvv)) (.classMem (.cv t) (syn_cvv))
      (.classMem (.cv u) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u))
          (syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)))
        (.classMem (syn_cop (syn_cop (.cv w) (.cv t)) (.cv u)) A))
      p0000 p0001 p0002 p0011
  have p0013 :=
    @g_eqoprriv w t u
      (syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A)) A
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0012
  exact p0013

@[expose]
noncomputable def g_oprabbi2i (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_oprabbi2i_1 : Nominal.NPrf
        (syn_wb (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) ph)) :
    Nominal.NPrf (.classEq A (syn_coprab x y z ph)) :=
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
    @g_oprabid2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_oprabbii (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) ph x y z
      dv_cache_0005 dv_cache_0006 hyp_oprabbi2i_1
  have p0002 :=
    @g_eqtr3i (syn_coprab x y z (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A))
      A (syn_coprab x y z ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elovex12 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_co B F C))
        (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) :=
  by
  have p0000 := @g_ne0i (syn_co B F C) A
  have p0001 := @g_opexb B C
  have p0002 := (Nominal.classEqRefl (syn_co B F C))
  have p0003 := @g_fvprc (syn_cop B C) F
  have p0004 :=
    @g_syl5eq (.neg (.classMem (syn_cop B C) (syn_cvv))) (syn_co B F C)
      (syn_cfv F (syn_cop B C)) (syn_c0) p0002 p0003
  have p0005 :=
    @g_sylnbir (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_cop B C) (syn_cvv)) (.classEq (syn_co B F C) (syn_c0)) p0001 p0004
  have p0006 :=
    @g_necon1ai (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_co B F C)
      (syn_c0) p0005
  have p0007 :=
    @g_syl (.classMem A (syn_co B F C)) (syn_wne (syn_co B F C) (syn_c0))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_elovex1 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_co B F C)) (.classMem B (syn_cvv))) :=
  by
  have p0000 := @g_elovex12 A B C F
  have p0001 :=
    @g_simpld (.classMem A (syn_co B F C)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      p0000
  exact p0001

@[expose]
noncomputable def g_elovex2 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_co B F C)) (.classMem C (syn_cvv))) :=
  by
  have p0000 := @g_elovex12 A B C F
  have p0001 :=
    @g_simprd (.classMem A (syn_co B F C)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
