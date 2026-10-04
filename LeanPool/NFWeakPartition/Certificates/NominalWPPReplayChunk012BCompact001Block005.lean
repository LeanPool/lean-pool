/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012BCompact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_trtxp`. -/
@[expose]
noncomputable def gTrtxp (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCtxp R S) (synCop B C))
        (synWa (synWbr A R B) (synWbr A S C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_S : t ∉ S.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have dv_cache_0001 : t ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((synCop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCcnv (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : t ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_R, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_y, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synWbr (.cv x) R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synCcnv (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0008 : t ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_S, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_z, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synWbr (.cv x) S (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_z, fresh_t_not_S, or_false,
          not_false_eq_true])
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
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((synWb (synWbr (.cv x) (synCtxp R S) (synCop B C))
          (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S C)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, fresh_z_not_C, fresh_z_not_R,
          fresh_z_not_S, or_false, not_false_eq_true])
  have dv_cache_0015 :
    y ∉
      ((synWb (synWbr (.cv x) (synCtxp R S) (synCop B (.cv z)))
          (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S (.cv z))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_ne_z, fresh_y_not_R,
          fresh_y_not_S, or_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (A).fv :=
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
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0017 :
    x ∉
      ((Wff.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
          (synWb (synWbr A (synCtxp R S) (synCop B C))
            (synWa (synWbr A R B) (synWbr A S C))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, fresh_x_not_R, fresh_x_not_S,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBrex A (synCop B C) (synCtxp R S)
  have p0001 := @gOpexb B C
  have p0002 :=
    @gAnbi2i (.classMem (synCop B C) (synCvv))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) (.classMem A (synCvv))
      p0001
  have p0003 :=
    @gSylib (synWbr A (synCtxp R S) (synCop B C))
      (synWa (.classMem A (synCvv)) (.classMem (synCop B C) (synCvv)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0000 p0002
  have p0004 := @gBrex A B R
  have p0005 := @gBrex A C S
  have p0006 :=
    @gAnim12i (synWbr A R B) (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWbr A S C) (synWa (.classMem A (synCvv)) (.classMem C (synCvv))) p0004 p0005
  have p0007 :=
    @gAnandi (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
  have p0008 :=
    @gSylibr (synWa (synWbr A R B) (synWbr A S C))
      (synWa (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (synWa (.classMem A (synCvv)) (.classMem C (synCvv))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0006 p0007
  have p0009 := @gBreq1 (.cv x) A (synCop B C) (synCtxp R S)
  have p0010 := @gBreq1 (.cv x) A B R
  have p0011 := @gBreq1 (.cv x) A C S
  have p0012 :=
    @gAnbi12d (.classEq (.cv x) A) (synWbr (.cv x) R B) (synWbr A R B)
      (synWbr (.cv x) S C) (synWbr A S C) p0010 p0011
  have p0013 :=
    @gBibi12d (.classEq (.cv x) A) (synWbr (.cv x) (synCtxp R S) (synCop B C))
      (synWbr A (synCtxp R S) (synCop B C))
      (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S C))
      (synWa (synWbr A R B) (synWbr A S C)) p0009 p0012
  have p0014 :=
    @gImbi2d (.classEq (.cv x) A)
      (synWb (synWbr (.cv x) (synCtxp R S) (synCop B C))
        (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S C)))
      (synWb (synWbr A (synCtxp R S) (synCop B C)) (synWa (synWbr A R B) (synWbr A S C)))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) p0013
  have p0015 := @gOpeq1 (.cv y) B (.cv z)
  have p0016 :=
    @gBreq2d (.classEq (.cv y) B) (synCop (.cv y) (.cv z)) (synCop B (.cv z)) (.cv x)
      (synCtxp R S) p0015
  have p0017 := @gBreq2 (.cv y) B (.cv x) R
  have p0018 :=
    @gAnbi1d (.classEq (.cv y) B) (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R B)
      (synWbr (.cv x) S (.cv z)) p0017
  have p0019 :=
    @gBibi12d (.classEq (.cv y) B)
      (synWbr (.cv x) (synCtxp R S) (synCop (.cv y) (.cv z)))
      (synWbr (.cv x) (synCtxp R S) (synCop B (.cv z)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))
      (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S (.cv z))) p0016 p0018
  have p0020 := @gOpeq2 (.cv z) C B
  have p0021 :=
    @gBreq2d (.classEq (.cv z) C) (synCop B (.cv z)) (synCop B C) (.cv x)
      (synCtxp R S) p0020
  have p0022 := @gBreq2 (.cv z) C (.cv x) S
  have p0023 :=
    @gAnbi2d (.classEq (.cv z) C) (synWbr (.cv x) S (.cv z)) (synWbr (.cv x) S C)
      (synWbr (.cv x) R B) p0022
  have p0024 :=
    @gBibi12d (.classEq (.cv z) C) (synWbr (.cv x) (synCtxp R S) (synCop B (.cv z)))
      (synWbr (.cv x) (synCtxp R S) (synCop B C))
      (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S (.cv z)))
      (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S C)) p0021 p0023
  have p0025 := (Nominal.classEqRefl (synCtxp R S))
  have p0026 :=
    @gBreqi (.cv x) (synCop (.cv y) (.cv z)) (synCtxp R S)
      (synCin (synCcom (synCcnv (synC1st)) R) (synCcom (synCcnv (synC2nd)) S))
      p0025
  have p0027 :=
    @gBrin (.cv x) (synCop (.cv y) (.cv z)) (synCcom (synCcnv (synC1st)) R)
      (synCcom (synCcnv (synC2nd)) S)
  have p0028 :=
    @gBrco t (.cv x) (synCop (.cv y) (.cv z)) (synCcnv (synC1st)) R dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0029 :=
    @gAncom (synWbr (.cv x) R (.cv t))
      (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z)))
  have p0030 := @gBrcnv (.cv t) (synCop (.cv y) (.cv z)) (synC1st)
  have p0031 := @gVex y
  have p0032 := @gVex z
  have p0033 := @gOpbr1st (.cv y) (.cv z) (.cv t) p0031 p0032
  have p0034 := @gEqucom y t
  have p0035_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv y) (.cv z)) (synC1st) (.cv t)) (.objEq y t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
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
      p0033
  have p0035 :=
    @gN3bitri (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z)))
      (synWbr (synCop (.cv y) (.cv z)) (synC1st) (.cv t)) (.objEq y t) (.objEq t y)
      p0030 p0035_e01_recanon p0034
  have p0036 :=
    @gAnbi1i (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z)))
      (.objEq t y) (synWbr (.cv x) R (.cv t)) p0035
  have p0037 :=
    @gBitri
      (synWa (synWbr (.cv x) R (.cv t))
        (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z))))
      (synWa (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z)))
        (synWbr (.cv x) R (.cv t)))
      (synWa (.objEq t y) (synWbr (.cv x) R (.cv t))) p0029 p0036
  have p0038 :=
    @gExbii
      (synWa (synWbr (.cv x) R (.cv t))
        (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z))))
      (synWa (.objEq t y) (synWbr (.cv x) R (.cv t))) t p0037
  have p0039 := @gBreq2 (.cv t) (.cv y) (.cv x) R
  have p0040 :=
    @gCeqsexv (synWbr (.cv x) R (.cv t)) (synWbr (.cv x) R (.cv y)) t (.cv y)
      dv_cache_0005 dv_cache_0006 p0031 p0039
  have p0041_e02_recanon :
    Nominal.NPrf
      (synWb (synWex t (synWa (.objEq t y) (synWbr (.cv x) R (.cv t))))
        (synWbr (.cv x) R (.cv y))) :=
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
      p0040
  have p0041 :=
    @gN3bitri
      (synWbr (.cv x) (synCcom (synCcnv (synC1st)) R) (synCop (.cv y) (.cv z)))
      (synWex t (synWa (synWbr (.cv x) R (.cv t))
          (synWbr (.cv t) (synCcnv (synC1st)) (synCop (.cv y) (.cv z)))))
      (synWex t (synWa (.objEq t y) (synWbr (.cv x) R (.cv t))))
      (synWbr (.cv x) R (.cv y)) p0028 p0038 p0041_e02_recanon
  have p0042 :=
    @gBrco t (.cv x) (synCop (.cv y) (.cv z)) (synCcnv (synC2nd)) S dv_cache_0001
      dv_cache_0002 dv_cache_0007 dv_cache_0008
  have p0043 :=
    @gAncom (synWbr (.cv x) S (.cv t))
      (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z)))
  have p0044 := @gBrcnv (.cv t) (synCop (.cv y) (.cv z)) (synC2nd)
  have p0045 := @gOpbr2nd (.cv y) (.cv z) (.cv t) p0031 p0032
  have p0046 := @gEqucom z t
  have p0047_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv y) (.cv z)) (synC2nd) (.cv t)) (.objEq z t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC2nd synCopab
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
      p0045
  have p0047 :=
    @gN3bitri (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z)))
      (synWbr (synCop (.cv y) (.cv z)) (synC2nd) (.cv t)) (.objEq z t) (.objEq t z)
      p0044 p0047_e01_recanon p0046
  have p0048 :=
    @gAnbi1i (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z)))
      (.objEq t z) (synWbr (.cv x) S (.cv t)) p0047
  have p0049 :=
    @gBitri
      (synWa (synWbr (.cv x) S (.cv t))
        (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z))))
      (synWa (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z)))
        (synWbr (.cv x) S (.cv t)))
      (synWa (.objEq t z) (synWbr (.cv x) S (.cv t))) p0043 p0048
  have p0050 :=
    @gExbii
      (synWa (synWbr (.cv x) S (.cv t))
        (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z))))
      (synWa (.objEq t z) (synWbr (.cv x) S (.cv t))) t p0049
  have p0051 := @gBreq2 (.cv t) (.cv z) (.cv x) S
  have p0052 :=
    @gCeqsexv (synWbr (.cv x) S (.cv t)) (synWbr (.cv x) S (.cv z)) t (.cv z)
      dv_cache_0009 dv_cache_0010 p0032 p0051
  have p0053_e02_recanon :
    Nominal.NPrf
      (synWb (synWex t (synWa (.objEq t z) (synWbr (.cv x) S (.cv t))))
        (synWbr (.cv x) S (.cv z))) :=
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
      p0052
  have p0053 :=
    @gN3bitri
      (synWbr (.cv x) (synCcom (synCcnv (synC2nd)) S) (synCop (.cv y) (.cv z)))
      (synWex t (synWa (synWbr (.cv x) S (.cv t))
          (synWbr (.cv t) (synCcnv (synC2nd)) (synCop (.cv y) (.cv z)))))
      (synWex t (synWa (.objEq t z) (synWbr (.cv x) S (.cv t))))
      (synWbr (.cv x) S (.cv z)) p0042 p0050 p0053_e02_recanon
  have p0054 :=
    @gAnbi12i
      (synWbr (.cv x) (synCcom (synCcnv (synC1st)) R) (synCop (.cv y) (.cv z)))
      (synWbr (.cv x) R (.cv y))
      (synWbr (.cv x) (synCcom (synCcnv (synC2nd)) S) (synCop (.cv y) (.cv z)))
      (synWbr (.cv x) S (.cv z)) p0041 p0053
  have p0055 :=
    @gN3bitri (synWbr (.cv x) (synCtxp R S) (synCop (.cv y) (.cv z)))
      (synWbr (.cv x)
        (synCin (synCcom (synCcnv (synC1st)) R) (synCcom (synCcnv (synC2nd)) S))
        (synCop (.cv y) (.cv z)))
      (synWa (synWbr (.cv x) (synCcom (synCcnv (synC1st)) R) (synCop (.cv y) (.cv z)))
        (synWbr (.cv x) (synCcom (synCcnv (synC2nd)) S) (synCop (.cv y) (.cv z))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))) p0026 p0027 p0054
  have p0056 :=
    @gVtocl2g
      (synWb (synWbr (.cv x) (synCtxp R S) (synCop (.cv y) (.cv z)))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))
      (synWb (synWbr (.cv x) (synCtxp R S) (synCop B (.cv z)))
        (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S (.cv z))))
      (synWb (synWbr (.cv x) (synCtxp R S) (synCop B C))
        (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S C)))
      y z B C (synCvv) (synCvv) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0019 p0024 p0055
  have p0057 :=
    @gVtoclg
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (synWb (synWbr (.cv x) (synCtxp R S) (synCop B C))
          (synWa (synWbr (.cv x) R B) (synWbr (.cv x) S C))))
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (synWb (synWbr A (synCtxp R S) (synCop B C))
          (synWa (synWbr A R B) (synWbr A S C))))
      x A (synCvv) dv_cache_0016 dv_cache_0017 p0014 p0056
  have p0058 :=
    @gImp (.classMem A (synCvv))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWb (synWbr A (synCtxp R S) (synCop B C)) (synWa (synWbr A R B) (synWbr A S C)))
      p0057
  have p0059 :=
    @gPm521nii (synWbr A (synCtxp R S) (synCop B C))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      (synWa (synWbr A R B) (synWbr A S C)) p0003 p0008 p0058
  exact p0059

/-- Checked nominal proof certificate identified upstream as `g_oteltxp`. -/
@[expose]
noncomputable def gOteltxp (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (synWb (.classMem (synCop A (synCop B C)) (synCtxp R S))
        (synWa (.classMem (synCop A B) R) (.classMem (synCop A C) S))) :=
  by
  have p0000 := @gTrtxp A B C R S
  have p0001 := (Nominal.biimpRefl (synWbr A (synCtxp R S) (synCop B C)))
  have p0002 := (Nominal.biimpRefl (synWbr A R B))
  have p0003 := (Nominal.biimpRefl (synWbr A S C))
  have p0004 :=
    @gAnbi12i (synWbr A R B) (.classMem (synCop A B) R) (synWbr A S C)
      (.classMem (synCop A C) S) p0002 p0003
  have p0005 :=
    @gN3bitr3i (synWbr A (synCtxp R S) (synCop B C))
      (synWa (synWbr A R B) (synWbr A S C))
      (.classMem (synCop A (synCop B C)) (synCtxp R S))
      (synWa (.classMem (synCop A B) R) (.classMem (synCop A C) S)) p0000 p0001 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_brtxp`. -/
@[expose]
noncomputable def gBrtxp (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (S : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWbr A (synCtxp R S) B) (synWex x (synWex y
            (synW3a (.classEq B (synCop (.cv x) (.cv y))) (synWbr A R (.cv x))
              (synWbr A S (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv
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
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
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
  have dv_cache_0003 : x ∉ ((synCcnv (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
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
  have dv_cache_0007 : y ∉ ((synCcnv (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0009 :
    y ∉ ((synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), dv_R_y, dv_B_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉ ((synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_S_x, dv_B_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Class.cv x)).fv :=
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
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0013 : w ∉ (B).fv :=
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
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classEq B (synCop (.cv x) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_B, fresh_w_ne_x, fresh_w_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classEq B (synCop (.cv w) (.cv y)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_w, fresh_z_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0017 : z ∉ ((Wff.classEq B (synCop (.cv x) (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_x, fresh_z_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0018 : w ∉ ((Wff.classEq B (synCop (.cv x) (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_B, fresh_w_ne_x, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0019 : z ∉ ((Class.cv y)).fv :=
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
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0021 :
    z ∉
      ((synWa (.classEq B (synCop (.cv x) (.cv y)))
          (.classEq B (synCop (.cv x) (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_x, fresh_z_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0022 :
    w ∉
      ((synWa (.classEq B (synCop (.cv x) (.cv y)))
          (.classEq B (synCop (.cv x) (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_B, fresh_w_ne_x, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0023 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 :=
    @gBrin A B (synCcom (synCcnv (synC1st)) R) (synCcom (synCcnv (synC2nd)) S)
  have p0001 :=
    @gBrco x A B (synCcnv (synC1st)) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0002 :=
    @gBrco y A B (synCcnv (synC2nd)) S dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008
  have p0003 :=
    @gAnbi12i (synWbr A (synCcom (synCcnv (synC1st)) R) B)
      (synWex x (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B)))
      (synWbr A (synCcom (synCcnv (synC2nd)) S) B)
      (synWex y (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)))
      p0001 p0002
  have p0004 :=
    @gBitri
      (synWbr A
        (synCin (synCcom (synCcnv (synC1st)) R) (synCcom (synCcnv (synC2nd)) S)) B)
      (synWa (synWbr A (synCcom (synCcnv (synC1st)) R) B)
        (synWbr A (synCcom (synCcnv (synC2nd)) S) B))
      (synWa (synWex x
          (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))) (synWex y
          (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B))))
      p0000 p0003
  have p0005 := (Nominal.classEqRefl (synCtxp R S))
  have p0006 :=
    @gBreqi A B (synCtxp R S)
      (synCin (synCcom (synCcnv (synC1st)) R) (synCcom (synCcnv (synC2nd)) S))
      p0005
  have p0007 :=
    @gEeanv (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))
      (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)) x y
      dv_cache_0009 dv_cache_0010
  have p0008 :=
    @gN3bitr4i
      (synWbr A
        (synCin (synCcom (synCcnv (synC1st)) R) (synCcom (synCcnv (synC2nd)) S)) B)
      (synWa (synWex x
          (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))) (synWex y
          (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B))))
      (synWbr A (synCtxp R S) B)
      (synWex x (synWex y
          (synWa (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))
            (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)))))
      p0004 p0006 p0007
  have p0009 :=
    @gAn4 (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B)
      (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)
  have p0010 :=
    @gAncom (synWa (synWbr A R (.cv x)) (synWbr A S (.cv y)))
      (.classEq B (synCop (.cv x) (.cv y)))
  have p0011 := @gBrcnv (.cv x) B (synC1st)
  have p0012 := @gVex x
  have p0013 := @gBr1st z B (.cv x) dv_cache_0011 dv_cache_0012 p0012
  have p0014 :=
    @gBitri (synWbr (.cv x) (synCcnv (synC1st)) B) (synWbr B (synC1st) (.cv x))
      (synWex z (.classEq B (synCop (.cv x) (.cv z)))) p0011 p0013
  have p0015 := @gBrcnv (.cv y) B (synC2nd)
  have p0016 := @gVex y
  have p0017 := @gBr2nd w B (.cv y) dv_cache_0013 dv_cache_0014 p0016
  have p0018 :=
    @gBitri (synWbr (.cv y) (synCcnv (synC2nd)) B) (synWbr B (synC2nd) (.cv y))
      (synWex w (.classEq B (synCop (.cv w) (.cv y)))) p0015 p0017
  have p0019 :=
    @gAnbi12i (synWbr (.cv x) (synCcnv (synC1st)) B)
      (synWex z (.classEq B (synCop (.cv x) (.cv z))))
      (synWbr (.cv y) (synCcnv (synC2nd)) B)
      (synWex w (.classEq B (synCop (.cv w) (.cv y)))) p0014 p0018
  have p0020 :=
    @gEeanv (.classEq B (synCop (.cv x) (.cv z))) (.classEq B (synCop (.cv w) (.cv y)))
      z w dv_cache_0015 dv_cache_0016
  have p0021 := @gEqtr2 B (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y))
  have p0022 := @gOpth (.cv x) (.cv z) (.cv w) (.cv y)
  have p0023_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y)))
        (synWa (.objEq x w) (.objEq z y))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gSimplbi (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y))) (.objEq x w)
      (.objEq z y) p0023_e00_recanon
  have p0024_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y)))
        (.classEq (.cv x) (.cv w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0023
  have p0024 :=
    @gEqcomd (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y))) (.cv x)
      (.cv w) p0024_e00_recanon
  have p0025 :=
    @gOpeq1d (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y))) (.cv w)
      (.cv x) (.cv y) p0024
  have p0026 :=
    @gSyl
      (synWa (.classEq B (synCop (.cv x) (.cv z))) (.classEq B (synCop (.cv w) (.cv y))))
      (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv w) (.cv y)))
      (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv x) (.cv y))) p0021 p0025
  have p0027 := @gEqeq1 B (synCop (.cv w) (.cv y)) (synCop (.cv x) (.cv y))
  have p0028 :=
    @gAdantl (.classEq B (synCop (.cv w) (.cv y)))
      (synWb (.classEq B (synCop (.cv x) (.cv y)))
        (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv x) (.cv y))))
      (.classEq B (synCop (.cv x) (.cv z))) p0027
  have p0029 :=
    @gMpbird
      (synWa (.classEq B (synCop (.cv x) (.cv z))) (.classEq B (synCop (.cv w) (.cv y))))
      (.classEq B (synCop (.cv x) (.cv y)))
      (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv x) (.cv y))) p0026 p0028
  have p0030 :=
    @gExlimivv
      (synWa (.classEq B (synCop (.cv x) (.cv z))) (.classEq B (synCop (.cv w) (.cv y))))
      (.classEq B (synCop (.cv x) (.cv y))) z w dv_cache_0017 dv_cache_0018 p0029
  have p0031 := @gOpeq2 (.cv z) (.cv y) (.cv x)
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (.classEq (synCop (.cv x) (.cv z)) (synCop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gEqeq2d (.objEq z y) (synCop (.cv x) (.cv z)) (synCop (.cv x) (.cv y)) B
      p0032_e00_recanon
  have p0033 := @gOpeq1 (.cv w) (.cv x) (.cv y)
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (.classEq (synCop (.cv w) (.cv y)) (synCop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @gEqeq2d (.objEq w x) (synCop (.cv w) (.cv y)) (synCop (.cv x) (.cv y)) B
      p0034_e00_recanon
  have p0035 :=
    @gBi2anan9 (.objEq z y) (.classEq B (synCop (.cv x) (.cv z)))
      (.classEq B (synCop (.cv x) (.cv y))) (.objEq w x)
      (.classEq B (synCop (.cv w) (.cv y))) (.classEq B (synCop (.cv x) (.cv y))) p0032
      p0034
  have p0036_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv z) (.cv y)) (.classEq (.cv w) (.cv x))) (synWb
          (synWa (.classEq B (synCop (.cv x) (.cv z))) (.classEq B (synCop (.cv w) (.cv y))))
          (synWa (.classEq B (synCop (.cv x) (.cv y)))
            (.classEq B (synCop (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0036 :=
    @gSpc2ev
      (synWa (.classEq B (synCop (.cv x) (.cv z))) (.classEq B (synCop (.cv w) (.cv y))))
      (synWa (.classEq B (synCop (.cv x) (.cv y))) (.classEq B (synCop (.cv x) (.cv y))))
      z w (.cv y) (.cv x) dv_cache_0019 dv_cache_0014 dv_cache_0012 dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0023 p0016 p0012 p0036_e02_recanon
  have p0037 :=
    @gAnidms (.classEq B (synCop (.cv x) (.cv y)))
      (synWex z (synWex w (synWa (.classEq B (synCop (.cv x) (.cv z)))
            (.classEq B (synCop (.cv w) (.cv y))))))
      p0036
  have p0038 :=
    @gImpbii
      (synWex z (synWex w (synWa (.classEq B (synCop (.cv x) (.cv z)))
            (.classEq B (synCop (.cv w) (.cv y))))))
      (.classEq B (synCop (.cv x) (.cv y))) p0030 p0037
  have p0039 :=
    @gN3bitr2i
      (synWa (synWbr (.cv x) (synCcnv (synC1st)) B)
        (synWbr (.cv y) (synCcnv (synC2nd)) B))
      (synWa (synWex z (.classEq B (synCop (.cv x) (.cv z))))
        (synWex w (.classEq B (synCop (.cv w) (.cv y)))))
      (synWex z (synWex w (synWa (.classEq B (synCop (.cv x) (.cv z)))
            (.classEq B (synCop (.cv w) (.cv y))))))
      (.classEq B (synCop (.cv x) (.cv y))) p0019 p0020 p0038
  have p0040 :=
    @gAnbi2i
      (synWa (synWbr (.cv x) (synCcnv (synC1st)) B)
        (synWbr (.cv y) (synCcnv (synC2nd)) B))
      (.classEq B (synCop (.cv x) (.cv y)))
      (synWa (synWbr A R (.cv x)) (synWbr A S (.cv y))) p0039
  have p0041 :=
    @gN3anass (.classEq B (synCop (.cv x) (.cv y))) (synWbr A R (.cv x))
      (synWbr A S (.cv y))
  have p0042 :=
    @gN3bitr4i
      (synWa (synWa (synWbr A R (.cv x)) (synWbr A S (.cv y)))
        (.classEq B (synCop (.cv x) (.cv y))))
      (synWa (.classEq B (synCop (.cv x) (.cv y)))
        (synWa (synWbr A R (.cv x)) (synWbr A S (.cv y))))
      (synWa (synWa (synWbr A R (.cv x)) (synWbr A S (.cv y)))
        (synWa (synWbr (.cv x) (synCcnv (synC1st)) B)
          (synWbr (.cv y) (synCcnv (synC2nd)) B)))
      (synW3a (.classEq B (synCop (.cv x) (.cv y))) (synWbr A R (.cv x))
        (synWbr A S (.cv y)))
      p0010 p0040 p0041
  have p0043 :=
    @gBitri
      (synWa (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))
        (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)))
      (synWa (synWa (synWbr A R (.cv x)) (synWbr A S (.cv y)))
        (synWa (synWbr (.cv x) (synCcnv (synC1st)) B)
          (synWbr (.cv y) (synCcnv (synC2nd)) B)))
      (synW3a (.classEq B (synCop (.cv x) (.cv y))) (synWbr A R (.cv x))
        (synWbr A S (.cv y)))
      p0009 p0042
  have p0044 :=
    @gN2exbii
      (synWa (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))
        (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)))
      (synW3a (.classEq B (synCop (.cv x) (.cv y))) (synWbr A R (.cv x))
        (synWbr A S (.cv y)))
      x y p0043
  have p0045 :=
    @gBitri (synWbr A (synCtxp R S) B)
      (synWex x (synWex y
          (synWa (synWa (synWbr A R (.cv x)) (synWbr (.cv x) (synCcnv (synC1st)) B))
            (synWa (synWbr A S (.cv y)) (synWbr (.cv y) (synCcnv (synC2nd)) B)))))
      (synWex x (synWex y
          (synW3a (.classEq B (synCop (.cv x) (.cv y))) (synWbr A R (.cv x))
            (synWbr A S (.cv y)))))
      p0008 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_txpexg`. -/
@[expose]
noncomputable def gTxpexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCtxp A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCtxp A B))
  have p0001 := @gN1stex
  have p0002 := @gCnvex (synC1st) p0001
  have p0003 := @gCoexg (synCcnv (synC1st)) A (synCvv) V
  have p0004 :=
    @gMpan (.classMem (synCcnv (synC1st)) (synCvv)) (.classMem A V)
      (.classMem (synCcom (synCcnv (synC1st)) A) (synCvv)) p0002 p0003
  have p0005 := @gN2ndex
  have p0006 := @gCnvex (synC2nd) p0005
  have p0007 := @gCoexg (synCcnv (synC2nd)) B (synCvv) W
  have p0008 :=
    @gMpan (.classMem (synCcnv (synC2nd)) (synCvv)) (.classMem B W)
      (.classMem (synCcom (synCcnv (synC2nd)) B) (synCvv)) p0006 p0007
  have p0009 :=
    @gInexg (synCcom (synCcnv (synC1st)) A) (synCcom (synCcnv (synC2nd)) B)
      (synCvv) (synCvv)
  have p0010 :=
    @gSyl2an (.classMem A V) (.classMem (synCcom (synCcnv (synC1st)) A) (synCvv))
      (.classMem (synCcom (synCcnv (synC2nd)) B) (synCvv))
      (.classMem (synCin (synCcom (synCcnv (synC1st)) A) (synCcom (synCcnv (synC2nd)) B))
        (synCvv))
      (.classMem B W) p0004 p0008 p0009
  have p0011 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCtxp A B)
      (synCin (synCcom (synCcnv (synC1st)) A) (synCcom (synCcnv (synC2nd)) B))
      (synCvv) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_txpex`. -/
@[expose]
noncomputable def gTxpex (A : Class) (B : Class)
    (hyp_txpex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_txpex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCtxp A B) (synCvv)) :=
  by
  have p0000 := @gTxpexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCtxp A B) (synCvv)) hyp_txpex_1 hyp_txpex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elfix`. -/
@[expose]
noncomputable def gElfix (A : Class) (R : Class) :
    Nominal.NPrf (synWb (.classMem A (synCfix R)) (synWbr A R A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
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
  have dv_cache_0002 : y ∉ ((synCin R (synCid))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_y_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synWbr (.cv x) R (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_R, or_false, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ ((Wff.classMem A (synCfix R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synWbr A R A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @gElex A (synCfix R)
  have p0001 := @gBrex A A R
  have p0002 :=
    @gSimpld (synWbr A R A) (.classMem A (synCvv)) (.classMem A (synCvv)) p0001
  have p0003 := @gEleq1 (.cv x) A (synCfix R)
  have p0004 := @gBreq12 (.cv x) A (.cv x) A R
  have p0005 :=
    @gAnidms (.classEq (.cv x) A) (synWb (synWbr (.cv x) R (.cv x)) (synWbr A R A))
      p0004
  have p0006 := (Nominal.classEqRefl (synCfix R))
  have p0007 := @gEleq2i (synCfix R) (synCrn (synCin R (synCid))) (.cv x) p0006
  have p0008 := @gElrn y (.cv x) (synCin R (synCid)) dv_cache_0001 dv_cache_0002
  have p0009 := @gBrin (.cv y) (.cv x) R (synCid)
  have p0010 := @gAncom (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) (synCid) (.cv x))
  have p0011 := @gVex x
  have p0012 := @gIdeq (.cv y) (.cv x) p0011
  have p0013_e00_recanon :
    Nominal.NPrf (synWb (synWbr (.cv y) (synCid) (.cv x)) (.objEq y x)) :=
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
      p0012
  have p0013 :=
    @gAnbi1i (synWbr (.cv y) (synCid) (.cv x)) (.objEq y x) (synWbr (.cv y) R (.cv x))
      p0013_e00_recanon
  have p0014 :=
    @gN3bitri (synWbr (.cv y) (synCin R (synCid)) (.cv x))
      (synWa (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) (synCid) (.cv x)))
      (synWa (synWbr (.cv y) (synCid) (.cv x)) (synWbr (.cv y) R (.cv x)))
      (synWa (.objEq y x) (synWbr (.cv y) R (.cv x))) p0009 p0010 p0013
  have p0015 :=
    @gExbii (synWbr (.cv y) (synCin R (synCid)) (.cv x))
      (synWa (.objEq y x) (synWbr (.cv y) R (.cv x))) y p0014
  have p0016 :=
    @gBitri (.classMem (.cv x) (synCrn (synCin R (synCid))))
      (synWex y (synWbr (.cv y) (synCin R (synCid)) (.cv x)))
      (synWex y (synWa (.objEq y x) (synWbr (.cv y) R (.cv x)))) p0008 p0015
  have p0017 := @gBreq1 (.cv y) (.cv x) (.cv x) R
  have p0018 :=
    @gCeqsexv (synWbr (.cv y) R (.cv x)) (synWbr (.cv x) R (.cv x)) y (.cv x)
      dv_cache_0001 dv_cache_0003 p0011 p0017
  have p0019_e02_recanon :
    Nominal.NPrf
      (synWb (synWex y (synWa (.objEq y x) (synWbr (.cv y) R (.cv x))))
        (synWbr (.cv x) R (.cv x))) :=
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
      p0018
  have p0019 :=
    @gN3bitri (.classMem (.cv x) (synCfix R))
      (.classMem (.cv x) (synCrn (synCin R (synCid))))
      (synWex y (synWa (.objEq y x) (synWbr (.cv y) R (.cv x))))
      (synWbr (.cv x) R (.cv x)) p0007 p0016 p0019_e02_recanon
  have p0020 :=
    @gVtoclbg (.classMem (.cv x) (synCfix R)) (synWbr (.cv x) R (.cv x))
      (.classMem A (synCfix R)) (synWbr A R A) x A (synCvv) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0003 p0005 p0019
  have p0021 :=
    @gPm521nii (.classMem A (synCfix R)) (.classMem A (synCvv)) (synWbr A R A) p0000
      p0002 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_fixexg`. -/
@[expose]
noncomputable def gFixexg (R : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem R V) (.classMem (synCfix R) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfix R))
  have p0001 := @gIdex
  have p0002 := @gInexg R (synCid) V (synCvv)
  have p0003 :=
    @gMpan2 (.classMem R V) (.classMem (synCid) (synCvv))
      (.classMem (synCin R (synCid)) (synCvv)) p0001 p0002
  have p0004 := @gRnexg (synCin R (synCid)) (synCvv)
  have p0005 :=
    @gSyl (.classMem R V) (.classMem (synCin R (synCid)) (synCvv))
      (.classMem (synCrn (synCin R (synCid))) (synCvv)) p0003 p0004
  have p0006 :=
    @gSyl5eqel (.classMem R V) (synCfix R) (synCrn (synCin R (synCid))) (synCvv)
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fixex`. -/
@[expose]
noncomputable def gFixex (R : Class)
    (hyp_fixex_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classMem (synCfix R) (synCvv)) :=
  by
  have p0000 := @gFixexg R (synCvv)
  have p0001 := Nominal.mp hyp_fixex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_op1st2nd`. -/
@[expose]
noncomputable def gOp1st2nd (A : Class) (B : Class) (C : Class)
    (hyp_op1st2nd_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_op1st2nd_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWa (synWbr C (synC1st) A) (synWbr C (synC2nd) B))
        (.classEq C (synCop A B))) :=
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
  have dv_cache_0003 :
    x ∉ ((Wff.imp (synWbr C (synC2nd) B) (.classEq C (synCop A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_C, fresh_x_not_B, fresh_x_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gBr1st x C A dv_cache_0001 dv_cache_0002 hyp_op1st2nd_1
  have p0001 := @gVex x
  have p0002 := @gOpbr2nd A (.cv x) B hyp_op1st2nd_1 p0001
  have p0003 :=
    @gBiimpi (synWbr (synCop A (.cv x)) (synC2nd) B) (.classEq (.cv x) B) p0002
  have p0004 := @gOpeq2d (synWbr (synCop A (.cv x)) (synC2nd) B) (.cv x) B A p0003
  have p0005 := @gBreq1 C (synCop A (.cv x)) B (synC2nd)
  have p0006 := @gEqeq1 C (synCop A (.cv x)) (synCop A B)
  have p0007 :=
    @gImbi12d (.classEq C (synCop A (.cv x))) (synWbr C (synC2nd) B)
      (synWbr (synCop A (.cv x)) (synC2nd) B) (.classEq C (synCop A B))
      (.classEq (synCop A (.cv x)) (synCop A B)) p0005 p0006
  have p0008 :=
    @gMpbiri (.classEq C (synCop A (.cv x)))
      (.imp (synWbr C (synC2nd) B) (.classEq C (synCop A B)))
      (.imp (synWbr (synCop A (.cv x)) (synC2nd) B)
        (.classEq (synCop A (.cv x)) (synCop A B)))
      p0004 p0007
  have p0009 :=
    @gExlimiv (.classEq C (synCop A (.cv x)))
      (.imp (synWbr C (synC2nd) B) (.classEq C (synCop A B))) x dv_cache_0003 p0008
  have p0010 :=
    @gSylbi (synWbr C (synC1st) A) (synWex x (.classEq C (synCop A (.cv x))))
      (.imp (synWbr C (synC2nd) B) (.classEq C (synCop A B))) p0000 p0009
  have p0011 :=
    @gImp (synWbr C (synC1st) A) (synWbr C (synC2nd) B) (.classEq C (synCop A B))
      p0010
  have p0012 := @gEqid A
  have p0013 := @gOpbr1st A B A hyp_op1st2nd_1 hyp_op1st2nd_2
  have p0014 := @gMpbir (synWbr (synCop A B) (synC1st) A) (.classEq A A) p0012 p0013
  have p0015 := @gEqid B
  have p0016 := @gOpbr2nd A B B hyp_op1st2nd_1 hyp_op1st2nd_2
  have p0017 := @gMpbir (synWbr (synCop A B) (synC2nd) B) (.classEq B B) p0015 p0016
  have p0018 :=
    @gPm32i (synWbr (synCop A B) (synC1st) A) (synWbr (synCop A B) (synC2nd) B)
      p0014 p0017
  have p0019 := @gBreq1 C (synCop A B) A (synC1st)
  have p0020 := @gBreq1 C (synCop A B) B (synC2nd)
  have p0021 :=
    @gAnbi12d (.classEq C (synCop A B)) (synWbr C (synC1st) A)
      (synWbr (synCop A B) (synC1st) A) (synWbr C (synC2nd) B)
      (synWbr (synCop A B) (synC2nd) B) p0019 p0020
  have p0022 :=
    @gMpbiri (.classEq C (synCop A B))
      (synWa (synWbr C (synC1st) A) (synWbr C (synC2nd) B))
      (synWa (synWbr (synCop A B) (synC1st) A) (synWbr (synCop A B) (synC2nd) B))
      p0018 p0021
  have p0023 :=
    @gImpbii (synWa (synWbr C (synC1st) A) (synWbr C (synC2nd) B))
      (.classEq C (synCop A B)) p0011 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_otelins2`. -/
@[expose]
noncomputable def gOtelins2 (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_otelins2_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop A (synCop B C)) (synCins2 R))
        (.classMem (synCop A C) R)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (synCop A (synCop B C)) (synCins2 R))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (synCop A C) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @gElex (synCop A (synCop B C)) (synCins2 R)
  have p0001 := @gOpexb A (synCop B C)
  have p0002 :=
    @gSimplbi (.classMem (synCop A (synCop B C)) (synCvv)) (.classMem A (synCvv))
      (.classMem (synCop B C) (synCvv)) p0001
  have p0003 :=
    @gSyl (.classMem (synCop A (synCop B C)) (synCins2 R))
      (.classMem (synCop A (synCop B C)) (synCvv)) (.classMem A (synCvv)) p0000 p0002
  have p0004 := @gElex (synCop A C) R
  have p0005 := @gOpexb A C
  have p0006 :=
    @gSimplbi (.classMem (synCop A C) (synCvv)) (.classMem A (synCvv))
      (.classMem C (synCvv)) p0005
  have p0007 :=
    @gSyl (.classMem (synCop A C) R) (.classMem (synCop A C) (synCvv))
      (.classMem A (synCvv)) p0004 p0006
  have p0008 := @gOpeq1 (.cv x) A (synCop B C)
  have p0009 :=
    @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) (synCop B C))
      (synCop A (synCop B C)) (synCins2 R) p0008
  have p0010 := @gOpeq1 (.cv x) A C
  have p0011 := @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) C) (synCop A C) R p0010
  have p0012 := @gVex x
  have p0013 := @gOpex (.cv x) B p0012 hyp_otelins2_1
  have p0014 := (Nominal.classEqRefl (synCins2 R))
  have p0015 :=
    @gEleq2i (synCins2 R) (synCtxp (synCvv) R) (synCop (.cv x) (synCop B C)) p0014
  have p0016 := @gOteltxp (.cv x) B C (synCvv) R
  have p0017 :=
    @gBitri (.classMem (synCop (.cv x) (synCop B C)) (synCins2 R))
      (.classMem (synCop (.cv x) (synCop B C)) (synCtxp (synCvv) R))
      (synWa (.classMem (synCop (.cv x) B) (synCvv)) (.classMem (synCop (.cv x) C) R))
      p0015 p0016
  have p0018 :=
    @gMpbiran (.classMem (synCop (.cv x) (synCop B C)) (synCins2 R))
      (.classMem (synCop (.cv x) B) (synCvv)) (.classMem (synCop (.cv x) C) R) p0013
      p0017
  have p0019 :=
    @gVtoclbg (.classMem (synCop (.cv x) (synCop B C)) (synCins2 R))
      (.classMem (synCop (.cv x) C) R)
      (.classMem (synCop A (synCop B C)) (synCins2 R)) (.classMem (synCop A C) R) x A
      (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009 p0011 p0018
  have p0020 :=
    @gPm521nii (.classMem (synCop A (synCop B C)) (synCins2 R))
      (.classMem A (synCvv)) (.classMem (synCop A C) R) p0003 p0007 p0019
  exact p0020


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_otelins3`. -/
@[expose]
noncomputable def gOtelins3 (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_otelins3_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop A (synCop B C)) (synCins3 R))
        (.classMem (synCop A B) R)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (synCop A (synCop B C)) (synCins3 R))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (synCop A B) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @gElex (synCop A (synCop B C)) (synCins3 R)
  have p0001 := @gOpexb A (synCop B C)
  have p0002 :=
    @gSimplbi (.classMem (synCop A (synCop B C)) (synCvv)) (.classMem A (synCvv))
      (.classMem (synCop B C) (synCvv)) p0001
  have p0003 :=
    @gSyl (.classMem (synCop A (synCop B C)) (synCins3 R))
      (.classMem (synCop A (synCop B C)) (synCvv)) (.classMem A (synCvv)) p0000 p0002
  have p0004 := @gElex (synCop A B) R
  have p0005 := @gOpexb A B
  have p0006 :=
    @gSimplbi (.classMem (synCop A B) (synCvv)) (.classMem A (synCvv))
      (.classMem B (synCvv)) p0005
  have p0007 :=
    @gSyl (.classMem (synCop A B) R) (.classMem (synCop A B) (synCvv))
      (.classMem A (synCvv)) p0004 p0006
  have p0008 := @gOpeq1 (.cv x) A (synCop B C)
  have p0009 :=
    @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) (synCop B C))
      (synCop A (synCop B C)) (synCins3 R) p0008
  have p0010 := @gOpeq1 (.cv x) A B
  have p0011 := @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) B) (synCop A B) R p0010
  have p0012 := @gVex x
  have p0013 := @gOpex (.cv x) C p0012 hyp_otelins3_1
  have p0014 := (Nominal.classEqRefl (synCins3 R))
  have p0015 :=
    @gEleq2i (synCins3 R) (synCtxp R (synCvv)) (synCop (.cv x) (synCop B C)) p0014
  have p0016 := @gOteltxp (.cv x) B C R (synCvv)
  have p0017 :=
    @gBitri (.classMem (synCop (.cv x) (synCop B C)) (synCins3 R))
      (.classMem (synCop (.cv x) (synCop B C)) (synCtxp R (synCvv)))
      (synWa (.classMem (synCop (.cv x) B) R) (.classMem (synCop (.cv x) C) (synCvv)))
      p0015 p0016
  have p0018 :=
    @gMpbiran2 (.classMem (synCop (.cv x) (synCop B C)) (synCins3 R))
      (.classMem (synCop (.cv x) B) R) (.classMem (synCop (.cv x) C) (synCvv)) p0013
      p0017
  have p0019 :=
    @gVtoclbg (.classMem (synCop (.cv x) (synCop B C)) (synCins3 R))
      (.classMem (synCop (.cv x) B) R)
      (.classMem (synCop A (synCop B C)) (synCins3 R)) (.classMem (synCop A B) R) x A
      (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009 p0011 p0018
  have p0020 :=
    @gPm521nii (.classMem (synCop A (synCop B C)) (synCins3 R))
      (.classMem A (synCvv)) (.classMem (synCop A B) R) p0003 p0007 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_brimage`. -/
@[expose]
noncomputable def gBrimage (A : Class) (B : Class) (R : Class)
    (hyp_brimage_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brimage_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr A (synCimage R) B) (.classEq B (synCima R A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have dv_cache_0001 : x ∉ ((synCop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi R)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
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
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synWbr (.cv t) (synCsset) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0008 :
    t ∉ ((synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_not_A, fresh_t_ne_x, fresh_t_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0010 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((synCsset)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((synCcnv (synCsi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_t_not_R,
          not_false_eq_true])
  have dv_cache_0013 : y ∉ (A).fv :=
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0014 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCima R A)).fv :=
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
          Finset.mem_union, fresh_x_not_R, fresh_x_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @gElima1c x (synCop A B)
      (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi R)))))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gElsymdif (synCop (synCsn (.cv x)) (synCop A B)) (synCins2 (synCsset))
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))
  have p0002 := @gOtelins2 (synCsn (.cv x)) A B (synCsset) hyp_brimage_1
  have p0003 := @gVex x
  have p0004 := @gOpelssetsn (.cv x) B p0003 hyp_brimage_2
  have p0005 :=
    @gBitri (.classMem (synCop (synCsn (.cv x)) (synCop A B)) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv x)) B) (synCsset)) (.classMem (.cv x) B) p0002
      p0004
  have p0006 :=
    @gOtelins3 (synCsn (.cv x)) A B (synCcom (synCsset) (synCcnv (synCsi R)))
      hyp_brimage_2
  have p0007 := @gBrcnv (synCsn (.cv x)) (.cv t) (synCsi R)
  have p0008 :=
    @gBrsnsi2 y (.cv x) (.cv t) R dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003
  have p0009 :=
    @gBitri (synWbr (synCsn (.cv x)) (synCcnv (synCsi R)) (.cv t))
      (synWbr (.cv t) (synCsi R) (synCsn (.cv x)))
      (synWex y (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x))))
      p0007 p0008
  have p0010 :=
    @gAnbi1i (synWbr (synCsn (.cv x)) (synCcnv (synCsi R)) (.cv t))
      (synWex y (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x))))
      (synWbr (.cv t) (synCsset) A) p0009
  have p0011 :=
    @gN1941v (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv t) (synCsset) A) y dv_cache_0006
  have p0012 :=
    @gBitr4i
      (synWa (synWbr (synCsn (.cv x)) (synCcnv (synCsi R)) (.cv t))
        (synWbr (.cv t) (synCsset) A))
      (synWa (synWex y
          (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x))))
        (synWbr (.cv t) (synCsset) A))
      (synWex y
        (synWa (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
          (synWbr (.cv t) (synCsset) A)))
      p0010 p0011
  have p0013 :=
    @gExbii
      (synWa (synWbr (synCsn (.cv x)) (synCcnv (synCsi R)) (.cv t))
        (synWbr (.cv t) (synCsset) A))
      (synWex y
        (synWa (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
          (synWbr (.cv t) (synCsset) A)))
      t p0012
  have p0014 :=
    @gExcom
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
        (synWbr (.cv t) (synCsset) A))
      t y
  have p0015 :=
    @gAnass (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x))
      (synWbr (.cv t) (synCsset) A)
  have p0016 :=
    @gExbii
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
        (synWbr (.cv t) (synCsset) A))
      (synWa (.classEq (.cv t) (synCsn (.cv y)))
        (synWa (synWbr (.cv y) R (.cv x)) (synWbr (.cv t) (synCsset) A)))
      t p0015
  have p0017 := @gSnex (.cv y)
  have p0018 := @gBreq1 (.cv t) (synCsn (.cv y)) A (synCsset)
  have p0019 :=
    @gAnbi2d (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv t) (synCsset) A)
      (synWbr (synCsn (.cv y)) (synCsset) A) (synWbr (.cv y) R (.cv x)) p0018
  have p0020 :=
    @gAncom (synWbr (.cv y) R (.cv x)) (synWbr (synCsn (.cv y)) (synCsset) A)
  have p0021 := @gVex y
  have p0022 := @gBrssetsn (.cv y) A p0021 hyp_brimage_1
  have p0023 :=
    @gAnbi1i (synWbr (synCsn (.cv y)) (synCsset) A) (.classMem (.cv y) A)
      (synWbr (.cv y) R (.cv x)) p0022
  have p0024 :=
    @gBitri
      (synWa (synWbr (.cv y) R (.cv x)) (synWbr (synCsn (.cv y)) (synCsset) A))
      (synWa (synWbr (synCsn (.cv y)) (synCsset) A) (synWbr (.cv y) R (.cv x)))
      (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x))) p0020 p0023
  have p0025 :=
    @gSyl6bb (.classEq (.cv t) (synCsn (.cv y)))
      (synWa (synWbr (.cv y) R (.cv x)) (synWbr (.cv t) (synCsset) A))
      (synWa (synWbr (.cv y) R (.cv x)) (synWbr (synCsn (.cv y)) (synCsset) A))
      (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x))) p0019 p0024
  have p0026 :=
    @gCeqsexv (synWa (synWbr (.cv y) R (.cv x)) (synWbr (.cv t) (synCsset) A))
      (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x))) t (synCsn (.cv y))
      dv_cache_0007 dv_cache_0008 p0017 p0025
  have p0027 :=
    @gBitri
      (synWex t
        (synWa (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
          (synWbr (.cv t) (synCsset) A)))
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y)))
          (synWa (synWbr (.cv y) R (.cv x)) (synWbr (.cv t) (synCsset) A))))
      (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x))) p0016 p0026
  have p0028 :=
    @gExbii
      (synWex t
        (synWa (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
          (synWbr (.cv t) (synCsset) A)))
      (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x))) y p0027
  have p0029 :=
    @gN3bitri
      (synWex t (synWa (synWbr (synCsn (.cv x)) (synCcnv (synCsi R)) (.cv t))
          (synWbr (.cv t) (synCsset) A)))
      (synWex t (synWex y (synWa
            (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
            (synWbr (.cv t) (synCsset) A))))
      (synWex y (synWex t (synWa
            (synWa (.classEq (.cv t) (synCsn (.cv y))) (synWbr (.cv y) R (.cv x)))
            (synWbr (.cv t) (synCsset) A))))
      (synWex y (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x)))) p0013 p0014
      p0028
  have p0030 :=
    @gOpelco t (synCsn (.cv x)) A (synCsset) (synCcnv (synCsi R)) dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0031 := @gElima2 y (.cv x) R A dv_cache_0003 dv_cache_0005 dv_cache_0013
  have p0032 :=
    @gN3bitr4i
      (synWex t (synWa (synWbr (synCsn (.cv x)) (synCcnv (synCsi R)) (.cv t))
          (synWbr (.cv t) (synCsset) A)))
      (synWex y (synWa (.classMem (.cv y) A) (synWbr (.cv y) R (.cv x))))
      (.classMem (synCop (synCsn (.cv x)) A) (synCcom (synCsset) (synCcnv (synCsi R))))
      (.classMem (.cv x) (synCima R A)) p0029 p0030 p0031
  have p0033 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop A B))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi R)))))
      (.classMem (synCop (synCsn (.cv x)) A) (synCcom (synCsset) (synCcnv (synCsi R))))
      (.classMem (.cv x) (synCima R A)) p0006 p0032
  have p0034 :=
    @gBibi12i
      (.classMem (synCop (synCsn (.cv x)) (synCop A B)) (synCins2 (synCsset)))
      (.classMem (.cv x) B)
      (.classMem (synCop (synCsn (.cv x)) (synCop A B))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi R)))))
      (.classMem (.cv x) (synCima R A)) p0005 p0033
  have p0035 :=
    @gXchbinx
      (.classMem (synCop (synCsn (.cv x)) (synCop A B)) (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))))
      (synWb (.classMem (synCop (synCsn (.cv x)) (synCop A B)) (synCins2 (synCsset)))
        (.classMem (synCop (synCsn (.cv x)) (synCop A B))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))))
      (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A))) p0001 p0034
  have p0036 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv x)) (synCop A B)) (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))))
      (.neg (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A)))) x p0035
  have p0037 :=
    @gExnal (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A))) x
  have p0038 :=
    @gN3bitri
      (.classMem (synCop A B) (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c)))
      (synWex x (.classMem (synCop (synCsn (.cv x)) (synCop A B))
          (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi R)))))))
      (synWex x (.neg (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A)))))
      (.neg (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A)))))
      p0000 p0036 p0037
  have p0039 :=
    @gCon2bii
      (.classMem (synCop A B) (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c)))
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A)))) p0038
  have p0040 := @gDfcleq x B (synCima R A) dv_cache_0014 dv_cache_0015
  have p0041 := (Nominal.classEqRefl (synCimage R))
  have p0042 :=
    @gBreqi A B (synCimage R)
      (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c)))
      p0041
  have p0043 :=
    (Nominal.biimpRefl (synWbr A (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
              (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c))) B))
  have p0044 := @gOpex A B hyp_brimage_1 hyp_brimage_2
  have p0045 :=
    @gElcompl (synCop A B)
      (synCima (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c))
      p0044
  have p0046 :=
    @gN3bitri (synWbr A (synCimage R) B)
      (synWbr A (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
              (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c))) B)
      (.classMem (synCop A B) (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
              (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c))))
      (.neg (.classMem (synCop A B) (synCima (synCsymdif (synCins2 (synCsset))
              (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c))))
      p0042 p0043 p0045
  have p0047 :=
    @gN3bitr4ri
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCima R A))))
      (.neg (.classMem (synCop A B) (synCima (synCsymdif (synCins2 (synCsset))
              (synCins3 (synCcom (synCsset) (synCcnv (synCsi R))))) (synC1c))))
      (.classEq B (synCima R A)) (synWbr A (synCimage R) B) p0039 p0040 p0046
  exact p0047


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_oqelins4`. -/
@[expose]
noncomputable def gOqelins4 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_oqelins4_4 : Nominal.NPrf (.classMem D (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
        (.classMem (synCop A (synCop B C)) R)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
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
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_z_ne_p : z ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_p_ne_b : p ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_p : b ≠ p := Ne.symm fresh_p_ne_b
  have fresh_p_ne_a : p ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_p : a ≠ p := Ne.symm fresh_p_ne_a
  have fresh_b_ne_a : b ≠ a :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_b : a ≠ b := Ne.symm fresh_b_ne_a
  have dv_cache_0001 : a ∉ ((synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_z, fresh_b_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_p, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_p, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 :
    a ∉
      ((synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    b ∉
      ((synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 : b ∉ ((Wff.objEq a x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x, or_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv x)).fv :=
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
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0012 :
    a ∉
      ((synWex b (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_x,
          fresh_a_ne_b, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_D,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_ne_z, fresh_p_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_b, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Class.cv b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_b, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((synCcom (synC1st) (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((synCcom (synC1st) (synC2nd))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : p ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show p ≠ a from (by exact fresh_p_ne_a))
  have dv_cache_0021 : p ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_y, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0023 : p ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_z, not_false_eq_true])
  have dv_cache_0024 : a ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0025 : a ∉ ((Wff.classEq (.cv b) (synCop (.cv y) (.cv z)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_y, fresh_a_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0026 : p ∉ ((Wff.classEq (.cv b) (synCop (.cv y) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_y, fresh_p_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0027 : b ∉ ((synCop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0028 :
    b ∉ ((Wff.classEq (.cv p) (synCop (.cv x) (synCop (.cv y) (.cv z))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_p, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_z,
          or_false, not_false_eq_true])
  have dv_cache_0029 :
    p ∉
      ((synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0031 : p ∉ ((synCop (.cv x) (synCop (.cv y) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0032 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0033 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0034 : z ∉ (C).fv :=
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
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0035 :
    z ∉
      ((synWb (.classMem (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R))
          (.classMem (synCop (.cv x) (synCop B C)) R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, fresh_z_not_C, fresh_z_not_D,
          fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0036 :
    y ∉
      ((synWb (.classMem (synCop (.cv x) (synCop B (synCop (.cv z) D))) (synCins4 R))
          (.classMem (synCop (.cv x) (synCop B (.cv z))) R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_ne_z, fresh_y_not_D,
          fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0037 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0038 :
    x ∉
      ((Wff.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
          (synWb (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
            (.classMem (synCop A (synCop B C)) R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, fresh_x_not_D, fresh_x_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gElex (synCop A (synCop B (synCop C D))) (synCins4 R)
  have p0001 := @gOpexb A (synCop B (synCop C D))
  have p0002 := @gOpexb B (synCop C D)
  have p0003 :=
    @gAnbi2i (.classMem (synCop B (synCop C D)) (synCvv))
      (synWa (.classMem B (synCvv)) (.classMem (synCop C D) (synCvv)))
      (.classMem A (synCvv)) p0002
  have p0004 :=
    @gBitri (.classMem (synCop A (synCop B (synCop C D))) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem (synCop B (synCop C D)) (synCvv)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem B (synCvv)) (.classMem (synCop C D) (synCvv))))
      p0001 p0003
  have p0005 := @gOpexb C D
  have p0006 :=
    @gSimplbi (.classMem (synCop C D) (synCvv)) (.classMem C (synCvv))
      (.classMem D (synCvv)) p0005
  have p0007 :=
    @gAnim2i (.classMem (synCop C D) (synCvv)) (.classMem C (synCvv))
      (.classMem B (synCvv)) p0006
  have p0008 :=
    @gAnim2i (synWa (.classMem B (synCvv)) (.classMem (synCop C D) (synCvv)))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) (.classMem A (synCvv))
      p0007
  have p0009 :=
    @gSylbi (.classMem (synCop A (synCop B (synCop C D))) (synCvv))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem B (synCvv)) (.classMem (synCop C D) (synCvv))))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0004 p0008
  have p0010 :=
    @gSyl (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
      (.classMem (synCop A (synCop B (synCop C D))) (synCvv))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0000 p0009
  have p0011 := @gElex (synCop A (synCop B C)) R
  have p0012 := @gOpexb A (synCop B C)
  have p0013 := @gOpexb B C
  have p0014 :=
    @gAnbi2i (.classMem (synCop B C) (synCvv))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) (.classMem A (synCvv))
      p0013
  have p0015 :=
    @gBitri (.classMem (synCop A (synCop B C)) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem (synCop B C) (synCvv)))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0012 p0014
  have p0016 :=
    @gSylib (.classMem (synCop A (synCop B C)) R)
      (.classMem (synCop A (synCop B C)) (synCvv))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      p0011 p0015
  have p0017 := @gOpeq1 (.cv x) A (synCop B (synCop C D))
  have p0018 :=
    @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) (synCop B (synCop C D)))
      (synCop A (synCop B (synCop C D))) (synCins4 R) p0017
  have p0019 := @gOpeq1 (.cv x) A (synCop B C)
  have p0020 :=
    @gEleq1d (.classEq (.cv x) A) (synCop (.cv x) (synCop B C))
      (synCop A (synCop B C)) R p0019
  have p0021 :=
    @gBibi12d (.classEq (.cv x) A)
      (.classMem (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R))
      (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
      (.classMem (synCop (.cv x) (synCop B C)) R)
      (.classMem (synCop A (synCop B C)) R) p0018 p0020
  have p0022 :=
    @gImbi2d (.classEq (.cv x) A)
      (synWb (.classMem (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R))
        (.classMem (synCop (.cv x) (synCop B C)) R))
      (synWb (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
        (.classMem (synCop A (synCop B C)) R))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv))) p0021
  have p0023 := @gOpeq1 (.cv y) B (synCop (.cv z) D)
  have p0024 :=
    @gOpeq2d (.classEq (.cv y) B) (synCop (.cv y) (synCop (.cv z) D))
      (synCop B (synCop (.cv z) D)) (.cv x) p0023
  have p0025 :=
    @gEleq1d (.classEq (.cv y) B) (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
      (synCop (.cv x) (synCop B (synCop (.cv z) D))) (synCins4 R) p0024
  have p0026 := @gOpeq1 (.cv y) B (.cv z)
  have p0027 :=
    @gOpeq2d (.classEq (.cv y) B) (synCop (.cv y) (.cv z)) (synCop B (.cv z)) (.cv x)
      p0026
  have p0028 :=
    @gEleq1d (.classEq (.cv y) B) (synCop (.cv x) (synCop (.cv y) (.cv z)))
      (synCop (.cv x) (synCop B (.cv z))) R p0027
  have p0029 :=
    @gBibi12d (.classEq (.cv y) B)
      (.classMem (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCins4 R))
      (.classMem (synCop (.cv x) (synCop B (synCop (.cv z) D))) (synCins4 R))
      (.classMem (synCop (.cv x) (synCop (.cv y) (.cv z))) R)
      (.classMem (synCop (.cv x) (synCop B (.cv z))) R) p0025 p0028
  have p0030 := @gOpeq1 (.cv z) C D
  have p0031 := @gOpeq2d (.classEq (.cv z) C) (synCop (.cv z) D) (synCop C D) B p0030
  have p0032 :=
    @gOpeq2d (.classEq (.cv z) C) (synCop B (synCop (.cv z) D))
      (synCop B (synCop C D)) (.cv x) p0031
  have p0033 :=
    @gEleq1d (.classEq (.cv z) C) (synCop (.cv x) (synCop B (synCop (.cv z) D)))
      (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R) p0032
  have p0034 := @gOpeq2 (.cv z) C B
  have p0035 :=
    @gOpeq2d (.classEq (.cv z) C) (synCop B (.cv z)) (synCop B C) (.cv x) p0034
  have p0036 :=
    @gEleq1d (.classEq (.cv z) C) (synCop (.cv x) (synCop B (.cv z)))
      (synCop (.cv x) (synCop B C)) R p0035
  have p0037 :=
    @gBibi12d (.classEq (.cv z) C)
      (.classMem (synCop (.cv x) (synCop B (synCop (.cv z) D))) (synCins4 R))
      (.classMem (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R))
      (.classMem (synCop (.cv x) (synCop B (.cv z))) R)
      (.classMem (synCop (.cv x) (synCop B C)) R) p0033 p0036
  have p0038 := (Nominal.classEqRefl (synCins4 R))
  have p0039 :=
    @gEleq2i (synCins4 R)
      (synCima (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))) R)
      (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) p0038
  have p0040 :=
    @gBrcnv (.cv p) (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
      (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))
  have p0041 :=
    @gBrtxp a b (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (.cv p)
      (synC1st)
      (synCtxp (synCcom (synC1st) (synC2nd))
        (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0042 :=
    @gN3ancoma (.classEq (.cv p) (synCop (.cv a) (.cv b)))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
  have p0043 :=
    @gN3anass
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
      (.classEq (.cv p) (synCop (.cv a) (.cv b)))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
  have p0044 := @gVex x
  have p0045 := @gVex y
  have p0046 := @gVex z
  have p0047 := @gOpex (.cv z) D p0046 hyp_oqelins4_4
  have p0048 := @gOpex (.cv y) (synCop (.cv z) D) p0045 p0047
  have p0049 :=
    @gOpbr1st (.cv x) (synCop (.cv y) (synCop (.cv z) D)) (.cv a) p0044 p0048
  have p0050 := @gEqucom x a
  have p0051_e00_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st)
          (.cv a)) (.objEq x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
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
      p0049
  have p0051 :=
    @gBitri
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
      (.objEq x a) (.objEq a x) p0051_e00_recanon p0050
  have p0052 :=
    @gAnbi1i
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
      (.objEq a x)
      (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      p0051
  have p0053 :=
    @gN3bitri
      (synW3a (.classEq (.cv p) (synCop (.cv a) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      (synW3a (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st)
          (.cv a)) (.classEq (.cv p) (synCop (.cv a) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      (synWa (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st)
          (.cv a)) (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      (synWa (.objEq a x) (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      p0042 p0043 p0052
  have p0054 :=
    @gExbii
      (synW3a (.classEq (.cv p) (synCop (.cv a) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      (synWa (.objEq a x) (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      b p0053
  have p0055 :=
    @gN1942v (.objEq a x)
      (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      b dv_cache_0010
  have p0056 :=
    @gBitri
      (synWex b (synW3a (.classEq (.cv p) (synCop (.cv a) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      (synWex b (synWa (.objEq a x) (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))))
      (synWa (.objEq a x) (synWex b (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))))
      p0054 p0055
  have p0057 :=
    @gExbii
      (synWex b (synW3a (.classEq (.cv p) (synCop (.cv a) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      (synWa (.objEq a x) (synWex b (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))))
      a p0056
  have p0058 := @gOpeq1 (.cv a) (.cv x) (.cv b)
  have p0059_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a x) (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv x) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @gEqeq2d (.objEq a x) (synCop (.cv a) (.cv b)) (synCop (.cv x) (.cv b)) (.cv p)
      p0059_e00_recanon
  have p0060 :=
    @gAnbi1d (.objEq a x) (.classEq (.cv p) (synCop (.cv a) (.cv b)))
      (.classEq (.cv p) (synCop (.cv x) (.cv b)))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
      p0059
  have p0061 :=
    @gExbidv (.objEq a x)
      (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      b dv_cache_0010 p0060
  have p0062_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv x)) (synWb (synWex b
            (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
              (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
                (synCtxp (synCcom (synC1st) (synC2nd))
                  (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))) (synWex b
            (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
              (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
                (synCtxp (synCcom (synC1st) (synC2nd))
                  (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synCop synCun synCnin synWnan synCcompl synWrex
          synCphi synWbr synCtxp synCin synCcom synCopab synCcnv synC1st
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0061
  have p0062 :=
    @gCeqsexv
      (synWex b (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      (synWex b (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      a (.cv x) dv_cache_0011 dv_cache_0012 p0044 p0062_e01_recanon
  have p0063_e02_recanon :
    Nominal.NPrf
      (synWb (synWex a (synWa (.objEq a x) (synWex b
              (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
                (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
                  (synCtxp (synCcom (synC1st) (synC2nd))
                    (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))))
        (synWex b (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))) :=
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
      p0062
  have p0063 :=
    @gN3bitri
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCtxp (synC1st)
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))) (.cv p))
      (synWex a (synWex b (synW3a (.classEq (.cv p) (synCop (.cv a) (.cv b)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synC1st) (.cv a))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))))
      (synWex a (synWa (.objEq a x) (synWex b
            (synWa (.classEq (.cv p) (synCop (.cv a) (.cv b)))
              (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
                (synCtxp (synCcom (synC1st) (synC2nd))
                  (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))))
      (synWex b (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      p0041 p0057 p0063_e02_recanon
  have p0064 :=
    @gAncom (.classEq (.cv p) (synCop (.cv x) (.cv b)))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
  have p0065 :=
    @gBrtxp p a (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (.cv b)
      (synCcom (synC1st) (synC2nd))
      (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) dv_cache_0013 dv_cache_0001
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020
  have p0066 :=
    @gN3anrot (.classEq (.cv b) (synCop (.cv p) (.cv a)))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCcom (synC1st) (synC2nd)) (.cv p))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a))
  have p0067 :=
    @gBrco2nd (.cv x) (synCop (.cv y) (synCop (.cv z) D)) (.cv p) (synC1st) p0044
      p0048
  have p0068 := @gOpbr1st (.cv y) (synCop (.cv z) D) (.cv p) p0045 p0047
  have p0069 := @gEqucom y p
  have p0070_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv y) (synCop (.cv z) D)) (synC1st) (.cv p))
        (.objEq y p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
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
      p0068
  have p0070 :=
    @gN3bitri
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCcom (synC1st) (synC2nd)) (.cv p))
      (synWbr (synCop (.cv y) (synCop (.cv z) D)) (synC1st) (.cv p)) (.objEq y p)
      (.objEq p y) p0067 p0070_e01_recanon p0069
  have p0071 :=
    @gBrco2nd (.cv x) (synCop (.cv y) (synCop (.cv z) D)) (.cv a)
      (synCcom (synC1st) (synC2nd)) p0044 p0048
  have p0072 := @gBrco2nd (.cv y) (synCop (.cv z) D) (.cv a) (synC1st) p0045 p0047
  have p0073 := @gOpbr1st (.cv z) D (.cv a) p0046 hyp_oqelins4_4
  have p0074_e01_recanon :
    Nominal.NPrf (synWb (synWbr (synCop (.cv z) D) (synC1st) (.cv a)) (.objEq z a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
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
      p0073
  have p0074 :=
    @gBitri
      (synWbr (synCop (.cv y) (synCop (.cv z) D)) (synCcom (synC1st) (synC2nd)) (.cv a))
      (synWbr (synCop (.cv z) D) (synC1st) (.cv a)) (.objEq z a) p0072
      p0074_e01_recanon
  have p0075 := @gEqucom z a
  have p0076 :=
    @gN3bitri
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a))
      (synWbr (synCop (.cv y) (synCop (.cv z) D)) (synCcom (synC1st) (synC2nd)) (.cv a))
      (.objEq z a) (.objEq a z) p0071 p0074 p0075
  have p0077 := @gBiid (.classEq (.cv b) (synCop (.cv p) (.cv a)))
  have p0078 :=
    @gN3anbi123i
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCcom (synC1st) (synC2nd)) (.cv p))
      (.objEq p y)
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a))
      (.objEq a z) (.classEq (.cv b) (synCop (.cv p) (.cv a)))
      (.classEq (.cv b) (synCop (.cv p) (.cv a))) p0070 p0076 p0077
  have p0079 :=
    @gBitri
      (synW3a (.classEq (.cv b) (synCop (.cv p) (.cv a)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCcom (synC1st) (synC2nd)) (.cv p))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a)))
      (synW3a (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCcom (synC1st) (synC2nd)) (.cv p))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a))
        (.classEq (.cv b) (synCop (.cv p) (.cv a))))
      (synW3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (synCop (.cv p) (.cv a))))
      p0066 p0078
  have p0080 :=
    @gN2exbii
      (synW3a (.classEq (.cv b) (synCop (.cv p) (.cv a)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCcom (synC1st) (synC2nd)) (.cv p))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a)))
      (synW3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (synCop (.cv p) (.cv a)))) p a
      p0079
  have p0081 := @gOpeq1 (.cv p) (.cv y) (.cv a)
  have p0082_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p y) (.classEq (synCop (.cv p) (.cv a)) (synCop (.cv y) (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0081
  have p0082 :=
    @gEqeq2d (.objEq p y) (synCop (.cv p) (.cv a)) (synCop (.cv y) (.cv a)) (.cv b)
      p0082_e00_recanon
  have p0083 := @gOpeq2 (.cv a) (.cv z) (.cv y)
  have p0084_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a z) (.classEq (synCop (.cv y) (.cv a)) (synCop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0083
  have p0084 :=
    @gEqeq2d (.objEq a z) (synCop (.cv y) (.cv a)) (synCop (.cv y) (.cv z)) (.cv b)
      p0084_e00_recanon
  have p0085_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (.cv y)) (synWb (.classEq (.cv b) (synCop (.cv p) (.cv a)))
          (.classEq (.cv b) (synCop (.cv y) (.cv a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0082
  have p0085_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv z)) (synWb (.classEq (.cv b) (synCop (.cv y) (.cv a)))
          (.classEq (.cv b) (synCop (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0084
  have p0085 :=
    @gCeqsex2v (.classEq (.cv b) (synCop (.cv p) (.cv a)))
      (.classEq (.cv b) (synCop (.cv y) (.cv a)))
      (.classEq (.cv b) (synCop (.cv y) (.cv z))) p a (.cv y) (.cv z) dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0020
      p0045 p0046 p0085_e02_recanon p0085_e03_recanon
  have p0086_e02_recanon :
    Nominal.NPrf
      (synWb (synWex p (synWex a (synW3a (.objEq p y) (.objEq a z)
              (.classEq (.cv b) (synCop (.cv p) (.cv a))))))
        (.classEq (.cv b) (synCop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synCop synCun synCnin synWnan synWa synCcompl synWrex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0085
  have p0086 :=
    @gN3bitri
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
      (synWex p (synWex a (synW3a (.classEq (.cv b) (synCop (.cv p) (.cv a)))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCcom (synC1st) (synC2nd)) (.cv p))
            (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) (.cv a)))))
      (synWex p (synWex a (synW3a (.objEq p y) (.objEq a z)
            (.classEq (.cv b) (synCop (.cv p) (.cv a))))))
      (.classEq (.cv b) (synCop (.cv y) (.cv z))) p0065 p0080 p0086_e02_recanon
  have p0087 :=
    @gAnbi1i
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
        (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
      (.classEq (.cv b) (synCop (.cv y) (.cv z)))
      (.classEq (.cv p) (synCop (.cv x) (.cv b))) p0086
  have p0088 :=
    @gBitri
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      (synWa (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))
        (.classEq (.cv p) (synCop (.cv x) (.cv b))))
      (synWa (.classEq (.cv b) (synCop (.cv y) (.cv z)))
        (.classEq (.cv p) (synCop (.cv x) (.cv b))))
      p0064 p0087
  have p0089 :=
    @gExbii
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
        (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b)))
      (synWa (.classEq (.cv b) (synCop (.cv y) (.cv z)))
        (.classEq (.cv p) (synCop (.cv x) (.cv b))))
      b p0088
  have p0090 := @gOpex (.cv y) (.cv z) p0045 p0046
  have p0091 := @gOpeq2 (.cv b) (synCop (.cv y) (.cv z)) (.cv x)
  have p0092 :=
    @gEqeq2d (.classEq (.cv b) (synCop (.cv y) (.cv z))) (synCop (.cv x) (.cv b))
      (synCop (.cv x) (synCop (.cv y) (.cv z))) (.cv p) p0091
  have p0093 :=
    @gCeqsexv (.classEq (.cv p) (synCop (.cv x) (.cv b)))
      (.classEq (.cv p) (synCop (.cv x) (synCop (.cv y) (.cv z)))) b
      (synCop (.cv y) (.cv z)) dv_cache_0027 dv_cache_0028 p0090 p0092
  have p0094 :=
    @gBitri
      (synWex b (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      (synWex b (synWa (.classEq (.cv b) (synCop (.cv y) (.cv z)))
          (.classEq (.cv p) (synCop (.cv x) (.cv b)))))
      (.classEq (.cv p) (synCop (.cv x) (synCop (.cv y) (.cv z)))) p0089 p0093
  have p0095 :=
    @gN3bitri
      (synWbr (.cv p) (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))))
        (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))))
      (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCtxp (synC1st)
          (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))) (.cv p))
      (synWex b (synWa (.classEq (.cv p) (synCop (.cv x) (.cv b)))
          (synWbr (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
            (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))) (.cv b))))
      (.classEq (.cv p) (synCop (.cv x) (synCop (.cv y) (.cv z)))) p0040 p0063 p0094
  have p0096 :=
    @gRexbii
      (synWbr (.cv p) (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))))
        (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))))
      (.classEq (.cv p) (synCop (.cv x) (synCop (.cv y) (.cv z)))) p R p0095
  have p0097 :=
    @gElima p (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))
      (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))))
      R dv_cache_0013 dv_cache_0029 dv_cache_0030
  have p0098 :=
    @gRisset p (synCop (.cv x) (synCop (.cv y) (.cv z))) R dv_cache_0031 dv_cache_0030
  have p0099 :=
    @gN3bitr4i
      (synWrex p R (synWbr (.cv p) (synCcnv (synCtxp (synC1st)
              (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))))
          (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D)))))
      (synWrex p R (.classEq (.cv p) (synCop (.cv x) (synCop (.cv y) (.cv z)))))
      (.classMem (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCima (synCcnv
            (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))) R))
      (.classMem (synCop (.cv x) (synCop (.cv y) (.cv z))) R) p0096 p0097 p0098
  have p0100 :=
    @gBitri
      (.classMem (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCins4 R))
      (.classMem (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCima (synCcnv
            (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
                (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))) R))
      (.classMem (synCop (.cv x) (synCop (.cv y) (.cv z))) R) p0039 p0099
  have p0101 :=
    @gVtocl2g
      (synWb (.classMem (synCop (.cv x) (synCop (.cv y) (synCop (.cv z) D))) (synCins4 R))
        (.classMem (synCop (.cv x) (synCop (.cv y) (.cv z))) R))
      (synWb (.classMem (synCop (.cv x) (synCop B (synCop (.cv z) D))) (synCins4 R))
        (.classMem (synCop (.cv x) (synCop B (.cv z))) R))
      (synWb (.classMem (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R))
        (.classMem (synCop (.cv x) (synCop B C)) R))
      y z B C (synCvv) (synCvv) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 p0029 p0037 p0100
  have p0102 :=
    @gVtoclg
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (synWb (.classMem (synCop (.cv x) (synCop B (synCop C D))) (synCins4 R))
          (.classMem (synCop (.cv x) (synCop B C)) R)))
      (.imp (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
        (synWb (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
          (.classMem (synCop A (synCop B C)) R)))
      x A (synCvv) dv_cache_0037 dv_cache_0038 p0022 p0101
  have p0103 :=
    @gImp (.classMem A (synCvv))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWb (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
        (.classMem (synCop A (synCop B C)) R))
      p0102
  have p0104 :=
    @gPm521nii (.classMem (synCop A (synCop B (synCop C D))) (synCins4 R))
      (synWa (.classMem A (synCvv)) (synWa (.classMem B (synCvv)) (.classMem C (synCvv))))
      (.classMem (synCop A (synCop B C)) R) p0010 p0016 p0103
  exact p0104


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ins2exg`. -/
@[expose]
noncomputable def gIns2exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCins2 A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCins2 A))
  have p0001 := @gVvex
  have p0002 := @gTxpexg (synCvv) A (synCvv) V
  have p0003 :=
    @gMpan (.classMem (synCvv) (synCvv)) (.classMem A V)
      (.classMem (synCtxp (synCvv) A) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem A V) (synCins2 A) (synCtxp (synCvv) A) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ins3exg`. -/
@[expose]
noncomputable def gIns3exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCins3 A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCins3 A))
  have p0001 := @gVvex
  have p0002 := @gTxpexg A (synCvv) V (synCvv)
  have p0003 :=
    @gMpan2 (.classMem A V) (.classMem (synCvv) (synCvv))
      (.classMem (synCtxp A (synCvv)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem A V) (synCins3 A) (synCtxp A (synCvv)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ins2ex`. -/
@[expose]
noncomputable def gIns2ex (A : Class)
    (hyp_insex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCins2 A) (synCvv)) :=
  by
  have p0000 := @gIns2exg A (synCvv)
  have p0001 := Nominal.mp hyp_insex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ins3ex`. -/
@[expose]
noncomputable def gIns3ex (A : Class)
    (hyp_insex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCins3 A) (synCvv)) :=
  by
  have p0000 := @gIns3exg A (synCvv)
  have p0001 := Nominal.mp hyp_insex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ins4ex`. -/
@[expose]
noncomputable def gIns4ex (A : Class)
    (hyp_insex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCins4 A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCins4 A))
  have p0001 := @gN1stex
  have p0003 := @gN2ndex
  have p0004 := @gCoex (synC1st) (synC2nd) p0001 p0003
  have p0006 := @gCoex (synCcom (synC1st) (synC2nd)) (synC2nd) p0004 p0003
  have p0007 :=
    @gTxpex (synCcom (synC1st) (synC2nd))
      (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)) p0004 p0006
  have p0008 :=
    @gTxpex (synC1st)
      (synCtxp (synCcom (synC1st) (synC2nd))
        (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))
      p0001 p0007
  have p0009 :=
    @gCnvex
      (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
          (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))
      p0008
  have p0010 :=
    @gImaex
      (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
            (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd)))))
      A p0009 hyp_insex_1
  have p0011 :=
    @gEqeltri (synCins4 A)
      (synCima (synCcnv (synCtxp (synC1st) (synCtxp (synCcom (synC1st) (synC2nd))
              (synCcom (synCcom (synC1st) (synC2nd)) (synC2nd))))) A)
      (synCvv) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_imageexg`. -/
@[expose]
noncomputable def gImageexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCimage A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCimage A))
  have p0001 := @gSiexg A V
  have p0002 := @gCnvexg (synCsi A) (synCvv)
  have p0003 := @gSsetex
  have p0004 := @gCoexg (synCsset) (synCcnv (synCsi A)) (synCvv) (synCvv)
  have p0005 :=
    @gMpan (.classMem (synCsset) (synCvv)) (.classMem (synCcnv (synCsi A)) (synCvv))
      (.classMem (synCcom (synCsset) (synCcnv (synCsi A))) (synCvv)) p0003 p0004
  have p0006 :=
    @gN3syl (.classMem A V) (.classMem (synCsi A) (synCvv))
      (.classMem (synCcnv (synCsi A)) (synCvv))
      (.classMem (synCcom (synCsset) (synCcnv (synCsi A))) (synCvv)) p0001 p0002
      p0005
  have p0007 := @gIns3exg (synCcom (synCsset) (synCcnv (synCsi A))) (synCvv)
  have p0009 := @gIns2ex (synCsset) p0003
  have p0010 :=
    @gSymdifexg (synCins2 (synCsset))
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))) (synCvv) (synCvv)
  have p0011 :=
    @gMpan (.classMem (synCins2 (synCsset)) (synCvv))
      (.classMem (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))) (synCvv))
      (.classMem (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synCvv))
      p0009 p0010
  have p0012 :=
    @gN3syl (.classMem A V)
      (.classMem (synCcom (synCsset) (synCcnv (synCsi A))) (synCvv))
      (.classMem (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))) (synCvv))
      (.classMem (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synCvv))
      p0006 p0007 p0011
  have p0013 := @gN1cex
  have p0014 :=
    @gImaexg
      (synCsymdif (synCins2 (synCsset))
        (synCins3 (synCcom (synCsset) (synCcnv (synCsi A)))))
      (synC1c) (synCvv) (synCvv)
  have p0015 :=
    @gMpan2
      (.classMem (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synCvv))
      (.classMem (synC1c) (synCvv))
      (.classMem (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c)) (synCvv))
      p0013 p0014
  have p0016 :=
    @gComplexg
      (synCima (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c))
      (synCvv)
  have p0017 :=
    @gN3syl (.classMem A V)
      (.classMem (synCsymdif (synCins2 (synCsset))
          (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synCvv))
      (.classMem (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c)) (synCvv))
      (.classMem (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
              (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c))) (synCvv))
      p0012 p0015 p0016
  have p0018 :=
    @gSyl5eqel (.classMem A V) (synCimage A)
      (synCcompl (synCima (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCcom (synCsset) (synCcnv (synCsi A))))) (synC1c)))
      (synCvv) p0000 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_imageex`. -/
@[expose]
noncomputable def gImageex (A : Class)
    (hyp_imageex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCimage A) (synCvv)) :=
  by
  have p0000 := @gImageexg A (synCvv)
  have p0001 := Nominal.mp hyp_imageex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dmtxp`. -/
@[expose]
noncomputable def gDmtxp (R : Class) (S : Class) :
    Nominal.NPrf (.classEq (synCdm (synCtxp R S)) (synCin (synCdm R) (synCdm S))) :=
  by
  let proofSupport : Finset Var := R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_S : p ∉ S.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_p_ne_y : p ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_p : y ≠ p := Ne.symm fresh_p_ne_y
  have fresh_p_ne_z : p ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_p : z ≠ p := Ne.symm fresh_p_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
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
  have dv_cache_0002 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_p, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0007 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0008 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 :
    p ∉ ((synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_R, fresh_p_ne_z,
          fresh_p_not_S, or_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((synCop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_z, or_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((synCtxp R S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          Finset.mem_union, fresh_p_not_R, fresh_p_not_S, or_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((synWbr (.cv x) R (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0015 : y ∉ ((synWbr (.cv x) S (.cv z))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((synCdm (synCtxp R S))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((synCin (synCdm R) (synCdm S))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @gBrtxp y z (.cv x) (.cv p) R S dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @gExbii (synWbr (.cv x) (synCtxp R S) (.cv p))
      (synWex y (synWex z (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z)))
            (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      p p0000
  have p0002 :=
    @gExrot3
      (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z))) (synWbr (.cv x) R (.cv y))
        (synWbr (.cv x) S (.cv z)))
      p y z
  have p0003 :=
    @gBitri (synWex p (synWbr (.cv x) (synCtxp R S) (.cv p)))
      (synWex p (synWex y (synWex z (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z)))
              (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))))
      (synWex y (synWex z (synWex p (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z)))
              (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))))
      p0001 p0002
  have p0004 :=
    @gN3anass (.classEq (.cv p) (synCop (.cv y) (.cv z))) (synWbr (.cv x) R (.cv y))
      (synWbr (.cv x) S (.cv z))
  have p0005 :=
    @gExbii
      (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z))) (synWbr (.cv x) R (.cv y))
        (synWbr (.cv x) S (.cv z)))
      (synWa (.classEq (.cv p) (synCop (.cv y) (.cv z)))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))
      p p0004
  have p0006 :=
    @gN1941v (.classEq (.cv p) (synCop (.cv y) (.cv z)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))) p dv_cache_0010
  have p0007 :=
    @gBitri
      (synWex p
        (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z))) (synWbr (.cv x) R (.cv y))
          (synWbr (.cv x) S (.cv z))))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv y) (.cv z)))
          (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      (synWa (synWex p (.classEq (.cv p) (synCop (.cv y) (.cv z))))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))
      p0005 p0006
  have p0008 := @gVex y
  have p0009 := @gVex z
  have p0010 := @gOpex (.cv y) (.cv z) p0008 p0009
  have p0011 := @gIsseti p (synCop (.cv y) (.cv z)) dv_cache_0011 p0010
  have p0012 :=
    @gBiantrur (synWex p (.classEq (.cv p) (synCop (.cv y) (.cv z))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))) p0011
  have p0013 :=
    @gBicomi (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))
      (synWa (synWex p (.classEq (.cv p) (synCop (.cv y) (.cv z))))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))
      p0012
  have p0014 :=
    @gBitri
      (synWex p
        (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z))) (synWbr (.cv x) R (.cv y))
          (synWbr (.cv x) S (.cv z))))
      (synWa (synWex p (.classEq (.cv p) (synCop (.cv y) (.cv z))))
        (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))) p0007 p0013
  have p0015 :=
    @gN2exbii
      (synWex p
        (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z))) (synWbr (.cv x) R (.cv y))
          (synWbr (.cv x) S (.cv z))))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))) y z p0014
  have p0016 :=
    @gBitri (synWex p (synWbr (.cv x) (synCtxp R S) (.cv p)))
      (synWex y (synWex z (synWex p (synW3a (.classEq (.cv p) (synCop (.cv y) (.cv z)))
              (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z))))))
      (synWex y (synWex z (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      p0003 p0015
  have p0017 := @gEldm p (.cv x) (synCtxp R S) dv_cache_0012 dv_cache_0013
  have p0018 := @gElin (.cv x) (synCdm R) (synCdm S)
  have p0019 := @gEldm y (.cv x) R dv_cache_0001 dv_cache_0005
  have p0020 := @gEldm z (.cv x) S dv_cache_0002 dv_cache_0008
  have p0021 :=
    @gAnbi12i (.classMem (.cv x) (synCdm R)) (synWex y (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv x) (synCdm S)) (synWex z (synWbr (.cv x) S (.cv z))) p0019 p0020
  have p0022 :=
    @gEeanv (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)) y z dv_cache_0014
      dv_cache_0015
  have p0023 :=
    @gBicomi
      (synWex y (synWex z (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      (synWa (synWex y (synWbr (.cv x) R (.cv y))) (synWex z (synWbr (.cv x) S (.cv z))))
      p0022
  have p0024 :=
    @gBitri (synWa (.classMem (.cv x) (synCdm R)) (.classMem (.cv x) (synCdm S)))
      (synWa (synWex y (synWbr (.cv x) R (.cv y))) (synWex z (synWbr (.cv x) S (.cv z))))
      (synWex y (synWex z (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      p0021 p0023
  have p0025 :=
    @gBitri (.classMem (.cv x) (synCin (synCdm R) (synCdm S)))
      (synWa (.classMem (.cv x) (synCdm R)) (.classMem (.cv x) (synCdm S)))
      (synWex y (synWex z (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      p0018 p0024
  have p0026 :=
    @gN3bitr4i (synWex p (synWbr (.cv x) (synCtxp R S) (.cv p)))
      (synWex y (synWex z (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) S (.cv z)))))
      (.classMem (.cv x) (synCdm (synCtxp R S)))
      (.classMem (.cv x) (synCin (synCdm R) (synCdm S))) p0016 p0017 p0025
  have p0027 :=
    @gEqriv x (synCdm (synCtxp R S)) (synCin (synCdm R) (synCdm S)) dv_cache_0016
      dv_cache_0017 p0026
  exact p0027


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fntxp`. -/
@[expose]
noncomputable def gFntxp (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (synWfn G B)) (synWfn (synCtxp F G) (synCin A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
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
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_G : c ∉ G.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
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
  have dv_cache_0007 : a ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_G, not_false_eq_true])
  have dv_cache_0008 : b ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_G, not_false_eq_true])
  have dv_cache_0009 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 : c ∉ ((Class.cv x)).fv :=
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
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Class.cv x)).fv :=
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
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_z, not_false_eq_true])
  have dv_cache_0013 : d ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_z, not_false_eq_true])
  have dv_cache_0014 : c ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_F, not_false_eq_true])
  have dv_cache_0015 : d ∉ (F).fv :=
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
        simp only [fresh_d_not_F, not_false_eq_true])
  have dv_cache_0016 : c ∉ (G).fv :=
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
        simp only [fresh_c_not_G, not_false_eq_true])
  have dv_cache_0017 : d ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_G, not_false_eq_true])
  have dv_cache_0018 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0019 :
    d ∉
      ((synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b))) (synWbr (.cv x) F (.cv a))
          (synWbr (.cv x) G (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_b, fresh_d_not_G, fresh_d_ne_y,
          fresh_d_ne_a, fresh_d_not_F, or_false, not_false_eq_true])
  have dv_cache_0020 :
    c ∉
      ((synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b))) (synWbr (.cv x) F (.cv a))
          (synWbr (.cv x) G (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_b, fresh_c_not_G, fresh_c_ne_y,
          fresh_c_ne_a, fresh_c_not_F, or_false, not_false_eq_true])
  have dv_cache_0021 :
    a ∉
      ((synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWbr (.cv x) F (.cv c))
          (synWbr (.cv x) G (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_d, fresh_a_not_G, fresh_a_ne_z,
          fresh_a_ne_c, fresh_a_not_F, or_false, not_false_eq_true])
  have dv_cache_0022 :
    b ∉
      ((synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWbr (.cv x) F (.cv c))
          (synWbr (.cv x) G (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_d, fresh_b_not_G, fresh_b_ne_z,
          fresh_b_ne_c, fresh_b_not_F, or_false, not_false_eq_true])
  have dv_cache_0023 : d ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0024 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0025 : c ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_z, or_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_z, or_false, not_false_eq_true])
  have dv_cache_0027 : c ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_c_not_F, fresh_c_not_G, or_false, not_false_eq_true])
  have dv_cache_0028 : d ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_d_not_F, fresh_d_not_G, or_false, not_false_eq_true])
  have dv_cache_0029 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0030 : b ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0031 : a ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_a_not_F, fresh_a_not_G, or_false, not_false_eq_true])
  have dv_cache_0032 : b ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_b_not_F, fresh_b_not_G, or_false, not_false_eq_true])
  have dv_cache_0033 : z ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0034 : x ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0035 : y ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0036 : x ∉ ((synCtxp F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          Finset.mem_union, fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0037 : y ∉ ((synCtxp F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          Finset.mem_union, fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0038 : z ∉ ((synCtxp F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          Finset.mem_union, fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0039 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0040 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0041 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @gBrtxp a b (.cv x) (.cv y) F G dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @gBrtxp c d (.cv x) (.cv z) F G dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0002 :=
    @gAnbi12i (synWbr (.cv x) (synCtxp F G) (.cv y))
      (synWex a (synWex b (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
            (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) G (.cv b)))))
      (synWbr (.cv x) (synCtxp F G) (.cv z))
      (synWex c (synWex d (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d)))
            (synWbr (.cv x) F (.cv c)) (synWbr (.cv x) G (.cv d)))))
      p0000 p0001
  have p0003 :=
    @gEe4anv
      (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b))) (synWbr (.cv x) F (.cv a))
        (synWbr (.cv x) G (.cv b)))
      (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWbr (.cv x) F (.cv c))
        (synWbr (.cv x) G (.cv d)))
      a b c d dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
  have p0004 :=
    @gBitr4i
      (synWa (synWbr (.cv x) (synCtxp F G) (.cv y)) (synWbr (.cv x) (synCtxp F G) (.cv z)))
      (synWa (synWex a (synWex b (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
              (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) G (.cv b))))) (synWex c (synWex d
            (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d)))
              (synWbr (.cv x) F (.cv c)) (synWbr (.cv x) G (.cv d))))))
      (synWex a (synWex b (synWex c (synWex d (synWa
                (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
                  (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) G (.cv b)))
                (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d)))
                  (synWbr (.cv x) F (.cv c)) (synWbr (.cv x) G (.cv d))))))))
      p0002 p0003
  have p0005 :=
    @gAn6 (.classEq (.cv y) (synCop (.cv a) (.cv b))) (synWbr (.cv x) F (.cv a))
      (synWbr (.cv x) G (.cv b)) (.classEq (.cv z) (synCop (.cv c) (.cv d)))
      (synWbr (.cv x) F (.cv c)) (synWbr (.cv x) G (.cv d))
  have p0006 := @gFununiq (.cv x) (.cv a) (.cv c) F
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWfun F) (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
        (.objEq a c)) :=
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
      p0006
  have p0007 :=
    @gN3expib (synWfun F) (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c))
      (.objEq a c) p0007_e00_recanon
  have p0008 := @gFununiq (.cv x) (.cv b) (.cv d) G
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWfun G) (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d)))
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
      p0008
  have p0009 :=
    @gN3expib (synWfun G) (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d))
      (.objEq b d) p0009_e00_recanon
  have p0010 :=
    @gIm2anan9 (synWfun F)
      (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c))) (.objEq a c)
      (synWfun G) (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d)))
      (.objEq b d) p0007 p0009
  have p0011 :=
    @gEqeq12 (.cv y) (synCop (.cv a) (.cv b)) (.cv z) (synCop (.cv c) (.cv d))
  have p0012 := @gOpth (.cv a) (.cv b) (.cv c) (.cv d)
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
          (.classEq (.cv z) (synCop (.cv c) (.cv d)))) (synWb (.objEq y z)
          (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv c) (.cv d))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCop synCun synCnin synWnan synCcompl synWrex synWex
          synCphi synWb
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
      p0011
  have p0013_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv c) (.cv d)))
        (synWa (.objEq a c) (.objEq b d))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @gSyl6bb
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (.objEq y z) (.classEq (synCop (.cv a) (.cv b)) (synCop (.cv c) (.cv d)))
      (synWa (.objEq a c) (.objEq b d)) p0013_e00_recanon p0013_e01_recanon
  have p0014 :=
    @gImbi2d
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (.objEq y z) (synWa (.objEq a c) (.objEq b d))
      (synWa (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
        (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d))))
      p0013
  have p0015 :=
    @gSyl5ibrcom (synWa (synWfun F) (synWfun G))
      (.imp (synWa (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
          (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d)))) (.objEq y z))
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (.imp (synWa (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
          (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d))))
        (synWa (.objEq a c) (.objEq b d)))
      p0010 p0014
  have p0016 :=
    @gExp4a (synWa (synWfun F) (synWfun G))
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
      (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d))) (.objEq y z) p0015
  have p0017 :=
    @gN3impd (synWa (synWfun F) (synWfun G))
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
      (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d))) (.objEq y z) p0016
  have p0018 :=
    @gSyl5bi
      (synWa (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b))) (synWbr (.cv x) F (.cv a))
          (synWbr (.cv x) G (.cv b)))
        (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWbr (.cv x) F (.cv c))
          (synWbr (.cv x) G (.cv d))))
      (synW3a (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
          (.classEq (.cv z) (synCop (.cv c) (.cv d))))
        (synWa (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) F (.cv c)))
        (synWa (synWbr (.cv x) G (.cv b)) (synWbr (.cv x) G (.cv d))))
      (synWa (synWfun F) (synWfun G)) (.objEq y z) p0005 p0017
  have p0019 :=
    @gExlimdvv (synWa (synWfun F) (synWfun G))
      (synWa (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b))) (synWbr (.cv x) F (.cv a))
          (synWbr (.cv x) G (.cv b)))
        (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWbr (.cv x) F (.cv c))
          (synWbr (.cv x) G (.cv d))))
      (.objEq y z) c d dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 p0018
  have p0020 :=
    @gExlimdvv (synWa (synWfun F) (synWfun G))
      (synWex c (synWex d (synWa (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
              (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) G (.cv b)))
            (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d)))
              (synWbr (.cv x) F (.cv c)) (synWbr (.cv x) G (.cv d))))))
      (.objEq y z) a b dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0019
  have p0021 :=
    @gSyl5bi
      (synWa (synWbr (.cv x) (synCtxp F G) (.cv y)) (synWbr (.cv x) (synCtxp F G) (.cv z)))
      (synWex a (synWex b (synWex c (synWex d (synWa
                (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
                  (synWbr (.cv x) F (.cv a)) (synWbr (.cv x) G (.cv b)))
                (synW3a (.classEq (.cv z) (synCop (.cv c) (.cv d)))
                  (synWbr (.cv x) F (.cv c)) (synWbr (.cv x) G (.cv d))))))))
      (synWa (synWfun F) (synWfun G)) (.objEq y z) p0004 p0020
  have p0022 :=
    @gAlrimiv (synWa (synWfun F) (synWfun G))
      (.imp (synWa (synWbr (.cv x) (synCtxp F G) (.cv y))
          (synWbr (.cv x) (synCtxp F G) (.cv z))) (.objEq y z))
      z dv_cache_0033 p0021
  have p0023 :=
    @gAlrimivv (synWa (synWfun F) (synWfun G))
      (.all z (.imp (synWa (synWbr (.cv x) (synCtxp F G) (.cv y))
            (synWbr (.cv x) (synCtxp F G) (.cv z))) (.objEq y z)))
      x y dv_cache_0034 dv_cache_0035 p0022
  have p0024 :=
    @gDffun2 x y z (synCtxp F G) dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
      dv_cache_0040 dv_cache_0041
  have p0025 :=
    @gSylibr (synWa (synWfun F) (synWfun G))
      (.all x (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCtxp F G) (.cv y))
                (synWbr (.cv x) (synCtxp F G) (.cv z))) (.objEq y z)))))
      (synWfun (synCtxp F G)) p0023 p0024
  have p0026 := @gDmtxp F G
  have p0027 := @gIneq12 (synCdm F) A (synCdm G) B
  have p0028 :=
    @gSyl5eq (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (synCdm (synCtxp F G)) (synCin (synCdm F) (synCdm G)) (synCin A B) p0026 p0027
  have p0029 :=
    @gAnim12i (synWa (synWfun F) (synWfun G)) (synWfun (synCtxp F G))
      (synWa (.classEq (synCdm F) A) (.classEq (synCdm G) B))
      (.classEq (synCdm (synCtxp F G)) (synCin A B)) p0025 p0028
  have p0030 :=
    @gAn4s (synWfun F) (synWfun G) (.classEq (synCdm F) A) (.classEq (synCdm G) B)
      (synWa (synWfun (synCtxp F G)) (.classEq (synCdm (synCtxp F G)) (synCin A B)))
      p0029
  have p0031 := (Nominal.biimpRefl (synWfn F A))
  have p0032 := (Nominal.biimpRefl (synWfn G B))
  have p0033 :=
    @gAnbi12i (synWfn F A) (synWa (synWfun F) (.classEq (synCdm F) A)) (synWfn G B)
      (synWa (synWfun G) (.classEq (synCdm G) B)) p0031 p0032
  have p0034 := (Nominal.biimpRefl (synWfn (synCtxp F G) (synCin A B)))
  have p0035 :=
    @gN3imtr4i
      (synWa (synWa (synWfun F) (.classEq (synCdm F) A))
        (synWa (synWfun G) (.classEq (synCdm G) B)))
      (synWa (synWfun (synCtxp F G)) (.classEq (synCdm (synCtxp F G)) (synCin A B)))
      (synWa (synWfn F A) (synWfn G B)) (synWfn (synCtxp F G) (synCin A B)) p0030
      p0033 p0034
  exact p0035


end NFChoice.DirectNominalPrf.WPPReplay

end
