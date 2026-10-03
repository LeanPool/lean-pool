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

@[expose]
noncomputable def g_trtxp (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C))
        (syn_wa (syn_wbr A R B) (syn_wbr A S C))) :=
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
  have dv_cache_0002 : t ∉ ((syn_cop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0003 : t ∉ ((syn_ccnv (syn_c1st))).fv :=
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
  have dv_cache_0006 : t ∉ ((syn_wbr (.cv x) R (.cv y))).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_ccnv (syn_c2nd))).fv :=
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
  have dv_cache_0010 : t ∉ ((syn_wbr (.cv x) S (.cv z))).fv :=
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
      ((syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C))
          (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)))).fv :=
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
      ((syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z)))
          (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z))))).fv :=
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
      ((Wff.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
          (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C))
            (syn_wa (syn_wbr A R B) (syn_wbr A S C))))).fv :=
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
  have p0000 := @g_brex A (syn_cop B C) (syn_ctxp R S)
  have p0001 := @g_opexb B C
  have p0002 :=
    @g_anbi2i (.classMem (syn_cop B C) (syn_cvv))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem A (syn_cvv))
      p0001
  have p0003 :=
    @g_sylib (syn_wbr A (syn_ctxp R S) (syn_cop B C))
      (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0000 p0002
  have p0004 := @g_brex A B R
  have p0005 := @g_brex A C S
  have p0006 :=
    @g_anim12i (syn_wbr A R B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wbr A S C) (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))) p0004 p0005
  have p0007 :=
    @g_anandi (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0008 :=
    @g_sylibr (syn_wa (syn_wbr A R B) (syn_wbr A S C))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (syn_wa (.classMem A (syn_cvv)) (.classMem C (syn_cvv))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0006 p0007
  have p0009 := @g_breq1 (.cv x) A (syn_cop B C) (syn_ctxp R S)
  have p0010 := @g_breq1 (.cv x) A B R
  have p0011 := @g_breq1 (.cv x) A C S
  have p0012 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wbr (.cv x) R B) (syn_wbr A R B)
      (syn_wbr (.cv x) S C) (syn_wbr A S C) p0010 p0011
  have p0013 :=
    @g_bibi12d (.classEq (.cv x) A) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C))
      (syn_wbr A (syn_ctxp R S) (syn_cop B C))
      (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C))
      (syn_wa (syn_wbr A R B) (syn_wbr A S C)) p0009 p0012
  have p0014 :=
    @g_imbi2d (.classEq (.cv x) A)
      (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C))
        (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)))
      (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0013
  have p0015 := @g_opeq1 (.cv y) B (.cv z)
  have p0016 :=
    @g_breq2d (.classEq (.cv y) B) (syn_cop (.cv y) (.cv z)) (syn_cop B (.cv z)) (.cv x)
      (syn_ctxp R S) p0015
  have p0017 := @g_breq2 (.cv y) B (.cv x) R
  have p0018 :=
    @g_anbi1d (.classEq (.cv y) B) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R B)
      (syn_wbr (.cv x) S (.cv z)) p0017
  have p0019 :=
    @g_bibi12d (.classEq (.cv y) B)
      (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))
      (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z))) p0016 p0018
  have p0020 := @g_opeq2 (.cv z) C B
  have p0021 :=
    @g_breq2d (.classEq (.cv z) C) (syn_cop B (.cv z)) (syn_cop B C) (.cv x)
      (syn_ctxp R S) p0020
  have p0022 := @g_breq2 (.cv z) C (.cv x) S
  have p0023 :=
    @g_anbi2d (.classEq (.cv z) C) (syn_wbr (.cv x) S (.cv z)) (syn_wbr (.cv x) S C)
      (syn_wbr (.cv x) R B) p0022
  have p0024 :=
    @g_bibi12d (.classEq (.cv z) C) (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z)))
      (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C))
      (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z)))
      (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)) p0021 p0023
  have p0025 := (Nominal.classEqRefl (syn_ctxp R S))
  have p0026 :=
    @g_breqi (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ctxp R S)
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S))
      p0025
  have p0027 :=
    @g_brin (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ccom (syn_ccnv (syn_c1st)) R)
      (syn_ccom (syn_ccnv (syn_c2nd)) S)
  have p0028 :=
    @g_brco t (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ccnv (syn_c1st)) R dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0029 :=
    @g_ancom (syn_wbr (.cv x) R (.cv t))
      (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))
  have p0030 := @g_brcnv (.cv t) (syn_cop (.cv y) (.cv z)) (syn_c1st)
  have p0031 := @g_vex y
  have p0032 := @g_vex z
  have p0033 := @g_opbr1st (.cv y) (.cv z) (.cv t) p0031 p0032
  have p0034 := @g_equcom y t
  have p0035_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c1st) (.cv t)) (.objEq y t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c1st) (.cv t)) (.objEq y t) (.objEq t y)
      p0030 p0035_e01_recanon p0034
  have p0036 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))
      (.objEq t y) (syn_wbr (.cv x) R (.cv t)) p0035
  have p0037 :=
    @g_bitri
      (syn_wa (syn_wbr (.cv x) R (.cv t))
        (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z))))
      (syn_wa (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))
        (syn_wbr (.cv x) R (.cv t)))
      (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t))) p0029 p0036
  have p0038 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv x) R (.cv t))
        (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z))))
      (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t))) t p0037
  have p0039 := @g_breq2 (.cv t) (.cv y) (.cv x) R
  have p0040 :=
    @g_ceqsexv (syn_wbr (.cv x) R (.cv t)) (syn_wbr (.cv x) R (.cv y)) t (.cv y)
      dv_cache_0005 dv_cache_0006 p0031 p0039
  have p0041_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex t (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t))))
        (syn_wbr (.cv x) R (.cv y))) :=
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
      p0040
  have p0041 :=
    @g_n_3bitri
      (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_cop (.cv y) (.cv z)))
      (syn_wex t (syn_wa (syn_wbr (.cv x) R (.cv t))
          (syn_wbr (.cv t) (syn_ccnv (syn_c1st)) (syn_cop (.cv y) (.cv z)))))
      (syn_wex t (syn_wa (.objEq t y) (syn_wbr (.cv x) R (.cv t))))
      (syn_wbr (.cv x) R (.cv y)) p0028 p0038 p0041_e02_recanon
  have p0042 :=
    @g_brco t (.cv x) (syn_cop (.cv y) (.cv z)) (syn_ccnv (syn_c2nd)) S dv_cache_0001
      dv_cache_0002 dv_cache_0007 dv_cache_0008
  have p0043 :=
    @g_ancom (syn_wbr (.cv x) S (.cv t))
      (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))
  have p0044 := @g_brcnv (.cv t) (syn_cop (.cv y) (.cv z)) (syn_c2nd)
  have p0045 := @g_opbr2nd (.cv y) (.cv z) (.cv t) p0031 p0032
  have p0046 := @g_equcom z t
  have p0047_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c2nd) (.cv t)) (.objEq z t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c2nd syn_copab
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
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (syn_cop (.cv y) (.cv z)) (syn_c2nd) (.cv t)) (.objEq z t) (.objEq t z)
      p0044 p0047_e01_recanon p0046
  have p0048 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))
      (.objEq t z) (syn_wbr (.cv x) S (.cv t)) p0047
  have p0049 :=
    @g_bitri
      (syn_wa (syn_wbr (.cv x) S (.cv t))
        (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z))))
      (syn_wa (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))
        (syn_wbr (.cv x) S (.cv t)))
      (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t))) p0043 p0048
  have p0050 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv x) S (.cv t))
        (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z))))
      (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t))) t p0049
  have p0051 := @g_breq2 (.cv t) (.cv z) (.cv x) S
  have p0052 :=
    @g_ceqsexv (syn_wbr (.cv x) S (.cv t)) (syn_wbr (.cv x) S (.cv z)) t (.cv z)
      dv_cache_0009 dv_cache_0010 p0032 p0051
  have p0053_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex t (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t))))
        (syn_wbr (.cv x) S (.cv z))) :=
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
      p0052
  have p0053 :=
    @g_n_3bitri
      (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c2nd)) S) (syn_cop (.cv y) (.cv z)))
      (syn_wex t (syn_wa (syn_wbr (.cv x) S (.cv t))
          (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (syn_cop (.cv y) (.cv z)))))
      (syn_wex t (syn_wa (.objEq t z) (syn_wbr (.cv x) S (.cv t))))
      (syn_wbr (.cv x) S (.cv z)) p0042 p0050 p0053_e02_recanon
  have p0054 :=
    @g_anbi12i
      (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c2nd)) S) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (.cv x) S (.cv z)) p0041 p0053
  have p0055 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop (.cv y) (.cv z)))
      (syn_wbr (.cv x)
        (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S))
        (syn_cop (.cv y) (.cv z)))
      (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_cop (.cv y) (.cv z)))
        (syn_wbr (.cv x) (syn_ccom (syn_ccnv (syn_c2nd)) S) (syn_cop (.cv y) (.cv z))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p0026 p0027 p0054
  have p0056 :=
    @g_vtocl2g
      (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop (.cv y) (.cv z)))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))
      (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B (.cv z)))
        (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S (.cv z))))
      (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C))
        (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C)))
      y z B C (syn_cvv) (syn_cvv) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0019 p0024 p0055
  have p0057 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wb (syn_wbr (.cv x) (syn_ctxp R S) (syn_cop B C))
          (syn_wa (syn_wbr (.cv x) R B) (syn_wbr (.cv x) S C))))
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C))
          (syn_wa (syn_wbr A R B) (syn_wbr A S C))))
      x A (syn_cvv) dv_cache_0016 dv_cache_0017 p0014 p0056
  have p0058 :=
    @g_imp (.classMem A (syn_cvv))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wb (syn_wbr A (syn_ctxp R S) (syn_cop B C)) (syn_wa (syn_wbr A R B) (syn_wbr A S C)))
      p0057
  have p0059 :=
    @g_pm5_21nii (syn_wbr A (syn_ctxp R S) (syn_cop B C))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      (syn_wa (syn_wbr A R B) (syn_wbr A S C)) p0003 p0008 p0058
  exact p0059

@[expose]
noncomputable def g_oteltxp (A : Class) (B : Class) (C : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A (syn_cop B C)) (syn_ctxp R S))
        (syn_wa (.classMem (syn_cop A B) R) (.classMem (syn_cop A C) S))) :=
  by
  have p0000 := @g_trtxp A B C R S
  have p0001 := (Nominal.biimpRefl (syn_wbr A (syn_ctxp R S) (syn_cop B C)))
  have p0002 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0003 := (Nominal.biimpRefl (syn_wbr A S C))
  have p0004 :=
    @g_anbi12i (syn_wbr A R B) (.classMem (syn_cop A B) R) (syn_wbr A S C)
      (.classMem (syn_cop A C) S) p0002 p0003
  have p0005 :=
    @g_n_3bitr3i (syn_wbr A (syn_ctxp R S) (syn_cop B C))
      (syn_wa (syn_wbr A R B) (syn_wbr A S C))
      (.classMem (syn_cop A (syn_cop B C)) (syn_ctxp R S))
      (syn_wa (.classMem (syn_cop A B) R) (.classMem (syn_cop A C) S)) p0000 p0001 p0004
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

@[expose]
noncomputable def g_brtxp (x : Var) (y : Var) (A : Class) (B : Class) (R : Class)
    (S : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_ctxp R S) B) (syn_wex x (syn_wex y
            (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x))
              (syn_wbr A S (.cv y)))))) :=
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
  have dv_cache_0003 : x ∉ ((syn_ccnv (syn_c1st))).fv :=
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
  have dv_cache_0007 : y ∉ ((syn_ccnv (syn_c2nd))).fv :=
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
    y ∉ ((syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))).fv :=
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
    x ∉ ((syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))).fv :=
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
  have dv_cache_0015 : w ∉ ((Wff.classEq B (syn_cop (.cv x) (.cv z)))).fv :=
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
  have dv_cache_0016 : z ∉ ((Wff.classEq B (syn_cop (.cv w) (.cv y)))).fv :=
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
  have dv_cache_0017 : z ∉ ((Wff.classEq B (syn_cop (.cv x) (.cv y)))).fv :=
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
  have dv_cache_0018 : w ∉ ((Wff.classEq B (syn_cop (.cv x) (.cv y)))).fv :=
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
      ((syn_wa (.classEq B (syn_cop (.cv x) (.cv y)))
          (.classEq B (syn_cop (.cv x) (.cv y))))).fv :=
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
      ((syn_wa (.classEq B (syn_cop (.cv x) (.cv y)))
          (.classEq B (syn_cop (.cv x) (.cv y))))).fv :=
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
    @g_brin A B (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)
  have p0001 :=
    @g_brco x A B (syn_ccnv (syn_c1st)) R dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0002 :=
    @g_brco y A B (syn_ccnv (syn_c2nd)) S dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008
  have p0003 :=
    @g_anbi12i (syn_wbr A (syn_ccom (syn_ccnv (syn_c1st)) R) B)
      (syn_wex x (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)))
      (syn_wbr A (syn_ccom (syn_ccnv (syn_c2nd)) S) B)
      (syn_wex y (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))
      p0001 p0002
  have p0004 :=
    @g_bitri
      (syn_wbr A
        (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) B)
      (syn_wa (syn_wbr A (syn_ccom (syn_ccnv (syn_c1st)) R) B)
        (syn_wbr A (syn_ccom (syn_ccnv (syn_c2nd)) S) B))
      (syn_wa (syn_wex x
          (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))) (syn_wex y
          (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))))
      p0000 p0003
  have p0005 := (Nominal.classEqRefl (syn_ctxp R S))
  have p0006 :=
    @g_breqi A B (syn_ctxp R S)
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S))
      p0005
  have p0007 :=
    @g_eeanv (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))
      (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)) x y
      dv_cache_0009 dv_cache_0010
  have p0008 :=
    @g_n_3bitr4i
      (syn_wbr A
        (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) R) (syn_ccom (syn_ccnv (syn_c2nd)) S)) B)
      (syn_wa (syn_wex x
          (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))) (syn_wex y
          (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))))
      (syn_wbr A (syn_ctxp R S) B)
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))
            (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))))
      p0004 p0006 p0007
  have p0009 :=
    @g_an4 (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)
      (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)
  have p0010 :=
    @g_ancom (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y)))
      (.classEq B (syn_cop (.cv x) (.cv y)))
  have p0011 := @g_brcnv (.cv x) B (syn_c1st)
  have p0012 := @g_vex x
  have p0013 := @g_br1st z B (.cv x) dv_cache_0011 dv_cache_0012 p0012
  have p0014 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B) (syn_wbr B (syn_c1st) (.cv x))
      (syn_wex z (.classEq B (syn_cop (.cv x) (.cv z)))) p0011 p0013
  have p0015 := @g_brcnv (.cv y) B (syn_c2nd)
  have p0016 := @g_vex y
  have p0017 := @g_br2nd w B (.cv y) dv_cache_0013 dv_cache_0014 p0016
  have p0018 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B) (syn_wbr B (syn_c2nd) (.cv y))
      (syn_wex w (.classEq B (syn_cop (.cv w) (.cv y)))) p0015 p0017
  have p0019 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)
      (syn_wex z (.classEq B (syn_cop (.cv x) (.cv z))))
      (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)
      (syn_wex w (.classEq B (syn_cop (.cv w) (.cv y)))) p0014 p0018
  have p0020 :=
    @g_eeanv (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y)))
      z w dv_cache_0015 dv_cache_0016
  have p0021 := @g_eqtr2 B (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))
  have p0022 := @g_opth (.cv x) (.cv z) (.cv w) (.cv y)
  have p0023_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y)))
        (syn_wa (.objEq x w) (.objEq z y))) :=
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
    @g_simplbi (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.objEq x w)
      (.objEq z y) p0023_e00_recanon
  have p0024_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y)))
        (.classEq (.cv x) (.cv w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0023
  have p0024 :=
    @g_eqcomd (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.cv x)
      (.cv w) p0024_e00_recanon
  have p0025 :=
    @g_opeq1d (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y))) (.cv w)
      (.cv x) (.cv y) p0024
  have p0026 :=
    @g_syl
      (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y))))
      (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv w) (.cv y)))
      (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))) p0021 p0025
  have p0027 := @g_eqeq1 B (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))
  have p0028 :=
    @g_adantl (.classEq B (syn_cop (.cv w) (.cv y)))
      (syn_wb (.classEq B (syn_cop (.cv x) (.cv y)))
        (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))))
      (.classEq B (syn_cop (.cv x) (.cv z))) p0027
  have p0029 :=
    @g_mpbird
      (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y))))
      (.classEq B (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y))) p0026 p0028
  have p0030 :=
    @g_exlimivv
      (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y))))
      (.classEq B (syn_cop (.cv x) (.cv y))) z w dv_cache_0017 dv_cache_0018 p0029
  have p0031 := @g_opeq2 (.cv z) (.cv y) (.cv x)
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (.classEq (syn_cop (.cv x) (.cv z)) (syn_cop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @g_eqeq2d (.objEq z y) (syn_cop (.cv x) (.cv z)) (syn_cop (.cv x) (.cv y)) B
      p0032_e00_recanon
  have p0033 := @g_opeq1 (.cv w) (.cv x) (.cv y)
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (.classEq (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @g_eqeq2d (.objEq w x) (syn_cop (.cv w) (.cv y)) (syn_cop (.cv x) (.cv y)) B
      p0034_e00_recanon
  have p0035 :=
    @g_bi2anan9 (.objEq z y) (.classEq B (syn_cop (.cv x) (.cv z)))
      (.classEq B (syn_cop (.cv x) (.cv y))) (.objEq w x)
      (.classEq B (syn_cop (.cv w) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y))) p0032
      p0034
  have p0036_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv z) (.cv y)) (.classEq (.cv w) (.cv x))) (syn_wb
          (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y))))
          (syn_wa (.classEq B (syn_cop (.cv x) (.cv y)))
            (.classEq B (syn_cop (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0036 :=
    @g_spc2ev
      (syn_wa (.classEq B (syn_cop (.cv x) (.cv z))) (.classEq B (syn_cop (.cv w) (.cv y))))
      (syn_wa (.classEq B (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv x) (.cv y))))
      z w (.cv y) (.cv x) dv_cache_0019 dv_cache_0014 dv_cache_0012 dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0023 p0016 p0012 p0036_e02_recanon
  have p0037 :=
    @g_anidms (.classEq B (syn_cop (.cv x) (.cv y)))
      (syn_wex z (syn_wex w (syn_wa (.classEq B (syn_cop (.cv x) (.cv z)))
            (.classEq B (syn_cop (.cv w) (.cv y))))))
      p0036
  have p0038 :=
    @g_impbii
      (syn_wex z (syn_wex w (syn_wa (.classEq B (syn_cop (.cv x) (.cv z)))
            (.classEq B (syn_cop (.cv w) (.cv y))))))
      (.classEq B (syn_cop (.cv x) (.cv y))) p0030 p0037
  have p0039 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)
        (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))
      (syn_wa (syn_wex z (.classEq B (syn_cop (.cv x) (.cv z))))
        (syn_wex w (.classEq B (syn_cop (.cv w) (.cv y)))))
      (syn_wex z (syn_wex w (syn_wa (.classEq B (syn_cop (.cv x) (.cv z)))
            (.classEq B (syn_cop (.cv w) (.cv y))))))
      (.classEq B (syn_cop (.cv x) (.cv y))) p0019 p0020 p0038
  have p0040 :=
    @g_anbi2i
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)
        (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B))
      (.classEq B (syn_cop (.cv x) (.cv y)))
      (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))) p0039
  have p0041 :=
    @g_n_3anass (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x))
      (syn_wbr A S (.cv y))
  have p0042 :=
    @g_n_3bitr4i
      (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y)))
        (.classEq B (syn_cop (.cv x) (.cv y))))
      (syn_wa (.classEq B (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y))))
      (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y)))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)
          (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))
      (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x))
        (syn_wbr A S (.cv y)))
      p0010 p0040 p0041
  have p0043 :=
    @g_bitri
      (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))
        (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))
      (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr A S (.cv y)))
        (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B)
          (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))
      (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x))
        (syn_wbr A S (.cv y)))
      p0009 p0042
  have p0044 :=
    @g_n_2exbii
      (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))
        (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))
      (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x))
        (syn_wbr A S (.cv y)))
      x y p0043
  have p0045 :=
    @g_bitri (syn_wbr A (syn_ctxp R S) B)
      (syn_wex x (syn_wex y
          (syn_wa (syn_wa (syn_wbr A R (.cv x)) (syn_wbr (.cv x) (syn_ccnv (syn_c1st)) B))
            (syn_wa (syn_wbr A S (.cv y)) (syn_wbr (.cv y) (syn_ccnv (syn_c2nd)) B)))))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq B (syn_cop (.cv x) (.cv y))) (syn_wbr A R (.cv x))
            (syn_wbr A S (.cv y)))))
      p0008 p0044
  exact p0045

@[expose]
noncomputable def g_txpexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_ctxp A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_ctxp A B))
  have p0001 := @g_n_1stex
  have p0002 := @g_cnvex (syn_c1st) p0001
  have p0003 := @g_coexg (syn_ccnv (syn_c1st)) A (syn_cvv) V
  have p0004 :=
    @g_mpan (.classMem (syn_ccnv (syn_c1st)) (syn_cvv)) (.classMem A V)
      (.classMem (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_cvv)) p0002 p0003
  have p0005 := @g_n_2ndex
  have p0006 := @g_cnvex (syn_c2nd) p0005
  have p0007 := @g_coexg (syn_ccnv (syn_c2nd)) B (syn_cvv) W
  have p0008 :=
    @g_mpan (.classMem (syn_ccnv (syn_c2nd)) (syn_cvv)) (.classMem B W)
      (.classMem (syn_ccom (syn_ccnv (syn_c2nd)) B) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_inexg (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B)
      (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl2an (.classMem A V) (.classMem (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_cvv))
      (.classMem (syn_ccom (syn_ccnv (syn_c2nd)) B) (syn_cvv))
      (.classMem (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B))
        (syn_cvv))
      (.classMem B W) p0004 p0008 p0009
  have p0011 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_ctxp A B)
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) B))
      (syn_cvv) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_txpex (A : Class) (B : Class)
    (hyp_txpex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_txpex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ctxp A B) (syn_cvv)) :=
  by
  have p0000 := @g_txpexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_ctxp A B) (syn_cvv)) hyp_txpex_1 hyp_txpex_2 p0000
  exact p0001

@[expose]
noncomputable def g_elfix (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cfix R)) (syn_wbr A R A)) :=
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
  have dv_cache_0002 : y ∉ ((syn_cin R (syn_cid))).fv :=
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
  have dv_cache_0003 : y ∉ ((syn_wbr (.cv x) R (.cv x))).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem A (syn_cfix R))).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_wbr A R A)).fv :=
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
  have p0000 := @g_elex A (syn_cfix R)
  have p0001 := @g_brex A A R
  have p0002 :=
    @g_simpld (syn_wbr A R A) (.classMem A (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 := @g_eleq1 (.cv x) A (syn_cfix R)
  have p0004 := @g_breq12 (.cv x) A (.cv x) A R
  have p0005 :=
    @g_anidms (.classEq (.cv x) A) (syn_wb (syn_wbr (.cv x) R (.cv x)) (syn_wbr A R A))
      p0004
  have p0006 := (Nominal.classEqRefl (syn_cfix R))
  have p0007 := @g_eleq2i (syn_cfix R) (syn_crn (syn_cin R (syn_cid))) (.cv x) p0006
  have p0008 := @g_elrn y (.cv x) (syn_cin R (syn_cid)) dv_cache_0001 dv_cache_0002
  have p0009 := @g_brin (.cv y) (.cv x) R (syn_cid)
  have p0010 := @g_ancom (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cid) (.cv x))
  have p0011 := @g_vex x
  have p0012 := @g_ideq (.cv y) (.cv x) p0011
  have p0013_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv y) (syn_cid) (.cv x)) (.objEq y x)) :=
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
      p0012
  have p0013 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_cid) (.cv x)) (.objEq y x) (syn_wbr (.cv y) R (.cv x))
      p0013_e00_recanon
  have p0014 :=
    @g_n_3bitri (syn_wbr (.cv y) (syn_cin R (syn_cid)) (.cv x))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cid) (.cv x)))
      (syn_wa (syn_wbr (.cv y) (syn_cid) (.cv x)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x))) p0009 p0010 p0013
  have p0015 :=
    @g_exbii (syn_wbr (.cv y) (syn_cin R (syn_cid)) (.cv x))
      (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x))) y p0014
  have p0016 :=
    @g_bitri (.classMem (.cv x) (syn_crn (syn_cin R (syn_cid))))
      (syn_wex y (syn_wbr (.cv y) (syn_cin R (syn_cid)) (.cv x)))
      (syn_wex y (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x)))) p0008 p0015
  have p0017 := @g_breq1 (.cv y) (.cv x) (.cv x) R
  have p0018 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv x) R (.cv x)) y (.cv x)
      dv_cache_0001 dv_cache_0003 p0011 p0017
  have p0019_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex y (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x))))
        (syn_wbr (.cv x) R (.cv x))) :=
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
      p0018
  have p0019 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cfix R))
      (.classMem (.cv x) (syn_crn (syn_cin R (syn_cid))))
      (syn_wex y (syn_wa (.objEq y x) (syn_wbr (.cv y) R (.cv x))))
      (syn_wbr (.cv x) R (.cv x)) p0007 p0016 p0019_e02_recanon
  have p0020 :=
    @g_vtoclbg (.classMem (.cv x) (syn_cfix R)) (syn_wbr (.cv x) R (.cv x))
      (.classMem A (syn_cfix R)) (syn_wbr A R A) x A (syn_cvv) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0003 p0005 p0019
  have p0021 :=
    @g_pm5_21nii (.classMem A (syn_cfix R)) (.classMem A (syn_cvv)) (syn_wbr A R A) p0000
      p0002 p0020
  exact p0021

@[expose]
noncomputable def g_fixexg (R : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem R V) (.classMem (syn_cfix R) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfix R))
  have p0001 := @g_idex
  have p0002 := @g_inexg R (syn_cid) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem R V) (.classMem (syn_cid) (syn_cvv))
      (.classMem (syn_cin R (syn_cid)) (syn_cvv)) p0001 p0002
  have p0004 := @g_rnexg (syn_cin R (syn_cid)) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem R V) (.classMem (syn_cin R (syn_cid)) (syn_cvv))
      (.classMem (syn_crn (syn_cin R (syn_cid))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem R V) (syn_cfix R) (syn_crn (syn_cin R (syn_cid))) (syn_cvv)
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_fixex (R : Class)
    (hyp_fixex_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfix R) (syn_cvv)) :=
  by
  have p0000 := @g_fixexg R (syn_cvv)
  have p0001 := Nominal.mp hyp_fixex_1 p0000
  exact p0001

@[expose]
noncomputable def g_op1st2nd (A : Class) (B : Class) (C : Class)
    (hyp_op1st2nd_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_op1st2nd_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B))
        (.classEq C (syn_cop A B))) :=
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
    x ∉ ((Wff.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B)))).fv :=
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
  have p0000 := @g_br1st x C A dv_cache_0001 dv_cache_0002 hyp_op1st2nd_1
  have p0001 := @g_vex x
  have p0002 := @g_opbr2nd A (.cv x) B hyp_op1st2nd_1 p0001
  have p0003 :=
    @g_biimpi (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.classEq (.cv x) B) p0002
  have p0004 := @g_opeq2d (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.cv x) B A p0003
  have p0005 := @g_breq1 C (syn_cop A (.cv x)) B (syn_c2nd)
  have p0006 := @g_eqeq1 C (syn_cop A (.cv x)) (syn_cop A B)
  have p0007 :=
    @g_imbi12d (.classEq C (syn_cop A (.cv x))) (syn_wbr C (syn_c2nd) B)
      (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B) (.classEq C (syn_cop A B))
      (.classEq (syn_cop A (.cv x)) (syn_cop A B)) p0005 p0006
  have p0008 :=
    @g_mpbiri (.classEq C (syn_cop A (.cv x)))
      (.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B)))
      (.imp (syn_wbr (syn_cop A (.cv x)) (syn_c2nd) B)
        (.classEq (syn_cop A (.cv x)) (syn_cop A B)))
      p0004 p0007
  have p0009 :=
    @g_exlimiv (.classEq C (syn_cop A (.cv x)))
      (.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B))) x dv_cache_0003 p0008
  have p0010 :=
    @g_sylbi (syn_wbr C (syn_c1st) A) (syn_wex x (.classEq C (syn_cop A (.cv x))))
      (.imp (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B))) p0000 p0009
  have p0011 :=
    @g_imp (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B) (.classEq C (syn_cop A B))
      p0010
  have p0012 := @g_eqid A
  have p0013 := @g_opbr1st A B A hyp_op1st2nd_1 hyp_op1st2nd_2
  have p0014 := @g_mpbir (syn_wbr (syn_cop A B) (syn_c1st) A) (.classEq A A) p0012 p0013
  have p0015 := @g_eqid B
  have p0016 := @g_opbr2nd A B B hyp_op1st2nd_1 hyp_op1st2nd_2
  have p0017 := @g_mpbir (syn_wbr (syn_cop A B) (syn_c2nd) B) (.classEq B B) p0015 p0016
  have p0018 :=
    @g_pm3_2i (syn_wbr (syn_cop A B) (syn_c1st) A) (syn_wbr (syn_cop A B) (syn_c2nd) B)
      p0014 p0017
  have p0019 := @g_breq1 C (syn_cop A B) A (syn_c1st)
  have p0020 := @g_breq1 C (syn_cop A B) B (syn_c2nd)
  have p0021 :=
    @g_anbi12d (.classEq C (syn_cop A B)) (syn_wbr C (syn_c1st) A)
      (syn_wbr (syn_cop A B) (syn_c1st) A) (syn_wbr C (syn_c2nd) B)
      (syn_wbr (syn_cop A B) (syn_c2nd) B) p0019 p0020
  have p0022 :=
    @g_mpbiri (.classEq C (syn_cop A B))
      (syn_wa (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B))
      (syn_wa (syn_wbr (syn_cop A B) (syn_c1st) A) (syn_wbr (syn_cop A B) (syn_c2nd) B))
      p0018 p0021
  have p0023 :=
    @g_impbii (syn_wa (syn_wbr C (syn_c1st) A) (syn_wbr C (syn_c2nd) B))
      (.classEq C (syn_cop A B)) p0011 p0022
  exact p0023

@[expose]
noncomputable def g_otelins2 (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_otelins2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R))
        (.classMem (syn_cop A C) R)) :=
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
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R))).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_cop A C) R)).fv :=
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
  have p0000 := @g_elex (syn_cop A (syn_cop B C)) (syn_cins2 R)
  have p0001 := @g_opexb A (syn_cop B C)
  have p0002 :=
    @g_simplbi (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem (syn_cop B C) (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R))
      (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv)) p0000 p0002
  have p0004 := @g_elex (syn_cop A C) R
  have p0005 := @g_opexb A C
  have p0006 :=
    @g_simplbi (.classMem (syn_cop A C) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem C (syn_cvv)) p0005
  have p0007 :=
    @g_syl (.classMem (syn_cop A C) R) (.classMem (syn_cop A C) (syn_cvv))
      (.classMem A (syn_cvv)) p0004 p0006
  have p0008 := @g_opeq1 (.cv x) A (syn_cop B C)
  have p0009 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B C))
      (syn_cop A (syn_cop B C)) (syn_cins2 R) p0008
  have p0010 := @g_opeq1 (.cv x) A C
  have p0011 := @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) C) (syn_cop A C) R p0010
  have p0012 := @g_vex x
  have p0013 := @g_opex (.cv x) B p0012 hyp_otelins2_1
  have p0014 := (Nominal.classEqRefl (syn_cins2 R))
  have p0015 :=
    @g_eleq2i (syn_cins2 R) (syn_ctxp (syn_cvv) R) (syn_cop (.cv x) (syn_cop B C)) p0014
  have p0016 := @g_oteltxp (.cv x) B C (syn_cvv) R
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins2 R))
      (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_ctxp (syn_cvv) R))
      (syn_wa (.classMem (syn_cop (.cv x) B) (syn_cvv)) (.classMem (syn_cop (.cv x) C) R))
      p0015 p0016
  have p0018 :=
    @g_mpbiran (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins2 R))
      (.classMem (syn_cop (.cv x) B) (syn_cvv)) (.classMem (syn_cop (.cv x) C) R) p0013
      p0017
  have p0019 :=
    @g_vtoclbg (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins2 R))
      (.classMem (syn_cop (.cv x) C) R)
      (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R)) (.classMem (syn_cop A C) R) x A
      (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009 p0011 p0018
  have p0020 :=
    @g_pm5_21nii (.classMem (syn_cop A (syn_cop B C)) (syn_cins2 R))
      (.classMem A (syn_cvv)) (.classMem (syn_cop A C) R) p0003 p0007 p0019
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

@[expose]
noncomputable def g_otelins3 (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_otelins3_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R))
        (.classMem (syn_cop A B) R)) :=
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
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R))).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_cop A B) R)).fv :=
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
  have p0000 := @g_elex (syn_cop A (syn_cop B C)) (syn_cins3 R)
  have p0001 := @g_opexb A (syn_cop B C)
  have p0002 :=
    @g_simplbi (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem (syn_cop B C) (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R))
      (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (.classMem A (syn_cvv)) p0000 p0002
  have p0004 := @g_elex (syn_cop A B) R
  have p0005 := @g_opexb A B
  have p0006 :=
    @g_simplbi (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv)) p0005
  have p0007 :=
    @g_syl (.classMem (syn_cop A B) R) (.classMem (syn_cop A B) (syn_cvv))
      (.classMem A (syn_cvv)) p0004 p0006
  have p0008 := @g_opeq1 (.cv x) A (syn_cop B C)
  have p0009 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B C))
      (syn_cop A (syn_cop B C)) (syn_cins3 R) p0008
  have p0010 := @g_opeq1 (.cv x) A B
  have p0011 := @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) B) (syn_cop A B) R p0010
  have p0012 := @g_vex x
  have p0013 := @g_opex (.cv x) C p0012 hyp_otelins3_1
  have p0014 := (Nominal.classEqRefl (syn_cins3 R))
  have p0015 :=
    @g_eleq2i (syn_cins3 R) (syn_ctxp R (syn_cvv)) (syn_cop (.cv x) (syn_cop B C)) p0014
  have p0016 := @g_oteltxp (.cv x) B C R (syn_cvv)
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins3 R))
      (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_ctxp R (syn_cvv)))
      (syn_wa (.classMem (syn_cop (.cv x) B) R) (.classMem (syn_cop (.cv x) C) (syn_cvv)))
      p0015 p0016
  have p0018 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins3 R))
      (.classMem (syn_cop (.cv x) B) R) (.classMem (syn_cop (.cv x) C) (syn_cvv)) p0013
      p0017
  have p0019 :=
    @g_vtoclbg (.classMem (syn_cop (.cv x) (syn_cop B C)) (syn_cins3 R))
      (.classMem (syn_cop (.cv x) B) R)
      (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R)) (.classMem (syn_cop A B) R) x A
      (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009 p0011 p0018
  have p0020 :=
    @g_pm5_21nii (.classMem (syn_cop A (syn_cop B C)) (syn_cins3 R))
      (.classMem A (syn_cvv)) (.classMem (syn_cop A B) R) p0003 p0007 p0019
  exact p0020

@[expose]
noncomputable def g_brimage (A : Class) (B : Class) (R : Class)
    (hyp_brimage_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brimage_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cimage R) B) (.classEq B (syn_cima R A))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cop A B)).fv := by
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
      ((syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_wbr (.cv t) (syn_csset) A)).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_csn (.cv y))).fv :=
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
    t ∉ ((syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x)))).fv :=
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
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0011 : t ∉ ((syn_csset)).fv :=
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
  have dv_cache_0012 : t ∉ ((syn_ccnv (syn_csi R))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cima R A)).fv :=
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
    @g_elima1c x (syn_cop A B)
      (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elsymdif (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset))
      (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))
  have p0002 := @g_otelins2 (syn_csn (.cv x)) A B (syn_csset) hyp_brimage_1
  have p0003 := @g_vex x
  have p0004 := @g_opelssetsn (.cv x) B p0003 hyp_brimage_2
  have p0005 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv x)) B) (syn_csset)) (.classMem (.cv x) B) p0002
      p0004
  have p0006 :=
    @g_otelins3 (syn_csn (.cv x)) A B (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))
      hyp_brimage_2
  have p0007 := @g_brcnv (syn_csn (.cv x)) (.cv t) (syn_csi R)
  have p0008 :=
    @g_brsnsi2 y (.cv x) (.cv t) R dv_cache_0003 dv_cache_0004 dv_cache_0005 p0003
  have p0009 :=
    @g_bitri (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t))
      (syn_wbr (.cv t) (syn_csi R) (syn_csn (.cv x)))
      (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))))
      p0007 p0008
  have p0010 :=
    @g_anbi1i (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t))
      (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))))
      (syn_wbr (.cv t) (syn_csset) A) p0009
  have p0011 :=
    @g_n_19_41v (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wbr (.cv t) (syn_csset) A) y dv_cache_0006
  have p0012 :=
    @g_bitr4i
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t))
        (syn_wbr (.cv t) (syn_csset) A))
      (syn_wa (syn_wex y
          (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))))
        (syn_wbr (.cv t) (syn_csset) A))
      (syn_wex y
        (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
          (syn_wbr (.cv t) (syn_csset) A)))
      p0010 p0011
  have p0013 :=
    @g_exbii
      (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t))
        (syn_wbr (.cv t) (syn_csset) A))
      (syn_wex y
        (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
          (syn_wbr (.cv t) (syn_csset) A)))
      t p0012
  have p0014 :=
    @g_excom
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
        (syn_wbr (.cv t) (syn_csset) A))
      t y
  have p0015 :=
    @g_anass (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x))
      (syn_wbr (.cv t) (syn_csset) A)
  have p0016 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
        (syn_wbr (.cv t) (syn_csset) A))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A)))
      t p0015
  have p0017 := @g_snex (.cv y)
  have p0018 := @g_breq1 (.cv t) (syn_csn (.cv y)) A (syn_csset)
  have p0019 :=
    @g_anbi2d (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv t) (syn_csset) A)
      (syn_wbr (syn_csn (.cv y)) (syn_csset) A) (syn_wbr (.cv y) R (.cv x)) p0018
  have p0020 :=
    @g_ancom (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csset) A)
  have p0021 := @g_vex y
  have p0022 := @g_brssetsn (.cv y) A p0021 hyp_brimage_1
  have p0023 :=
    @g_anbi1i (syn_wbr (syn_csn (.cv y)) (syn_csset) A) (.classMem (.cv y) A)
      (syn_wbr (.cv y) R (.cv x)) p0022
  have p0024 :=
    @g_bitri
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csset) A))
      (syn_wa (syn_wbr (syn_csn (.cv y)) (syn_csset) A) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) p0020 p0023
  have p0025 :=
    @g_syl6bb (.classEq (.cv t) (syn_csn (.cv y)))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (syn_csn (.cv y)) (syn_csset) A))
      (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) p0019 p0024
  have p0026 :=
    @g_ceqsexv (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A))
      (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) t (syn_csn (.cv y))
      dv_cache_0007 dv_cache_0008 p0017 p0025
  have p0027 :=
    @g_bitri
      (syn_wex t
        (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
          (syn_wbr (.cv t) (syn_csset) A)))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
          (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv t) (syn_csset) A))))
      (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) p0016 p0026
  have p0028 :=
    @g_exbii
      (syn_wex t
        (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
          (syn_wbr (.cv t) (syn_csset) A)))
      (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))) y p0027
  have p0029 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t))
          (syn_wbr (.cv t) (syn_csset) A)))
      (syn_wex t (syn_wex y (syn_wa
            (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
            (syn_wbr (.cv t) (syn_csset) A))))
      (syn_wex y (syn_wex t (syn_wa
            (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (syn_wbr (.cv y) R (.cv x)))
            (syn_wbr (.cv t) (syn_csset) A))))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x)))) p0013 p0014
      p0028
  have p0030 :=
    @g_opelco t (syn_csn (.cv x)) A (syn_csset) (syn_ccnv (syn_csi R)) dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0031 := @g_elima2 y (.cv x) R A dv_cache_0003 dv_cache_0005 dv_cache_0013
  have p0032 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (syn_wbr (syn_csn (.cv x)) (syn_ccnv (syn_csi R)) (.cv t))
          (syn_wbr (.cv t) (syn_csset) A)))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wbr (.cv y) R (.cv x))))
      (.classMem (syn_cop (syn_csn (.cv x)) A) (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))
      (.classMem (.cv x) (syn_cima R A)) p0029 p0030 p0031
  have p0033 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))
      (.classMem (syn_cop (syn_csn (.cv x)) A) (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))
      (.classMem (.cv x) (syn_cima R A)) p0006 p0032
  have p0034 :=
    @g_bibi12i
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset)))
      (.classMem (.cv x) B)
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))
      (.classMem (.cv x) (syn_cima R A)) p0005 p0033
  have p0035 :=
    @g_xchbinx
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))))
      (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_cins2 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))))
      (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))) p0001 p0034
  have p0036 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B)) (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))))
      (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))) x p0035
  have p0037 :=
    @g_exnal (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))) x
  have p0038 :=
    @g_n_3bitri
      (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)))
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop A B))
          (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R)))))))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))))
      (.neg (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))))
      p0000 p0036 p0037
  have p0039 :=
    @g_con2bii
      (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)))
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A)))) p0038
  have p0040 := @g_dfcleq x B (syn_cima R A) dv_cache_0014 dv_cache_0015
  have p0041 := (Nominal.classEqRefl (syn_cimage R))
  have p0042 :=
    @g_breqi A B (syn_cimage R)
      (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c)))
      p0041
  have p0043 :=
    (Nominal.biimpRefl (syn_wbr A (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
              (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) B))
  have p0044 := @g_opex A B hyp_brimage_1 hyp_brimage_2
  have p0045 :=
    @g_elcompl (syn_cop A B)
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))
      p0044
  have p0046 :=
    @g_n_3bitri (syn_wbr A (syn_cimage R) B)
      (syn_wbr A (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
              (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))) B)
      (.classMem (syn_cop A B) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
              (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))))
      (.neg (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
              (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))))
      p0042 p0043 p0045
  have p0047 :=
    @g_n_3bitr4ri
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cima R A))))
      (.neg (.classMem (syn_cop A B) (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
              (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi R))))) (syn_c1c))))
      (.classEq B (syn_cima R A)) (syn_wbr A (syn_cimage R) B) p0039 p0040 p0046
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

@[expose]
noncomputable def g_oqelins4 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_oqelins4_4 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
        (.classMem (syn_cop A (syn_cop B C)) R)) :=
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
  have dv_cache_0001 : a ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))).fv :=
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
  have dv_cache_0002 : b ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))).fv :=
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
  have dv_cache_0005 : a ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0006 : b ∉ ((syn_c1st)).fv :=
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
      ((syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))).fv :=
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
      ((syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))).fv :=
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
      ((syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))).fv :=
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
  have dv_cache_0013 : p ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))).fv :=
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
  have dv_cache_0016 : p ∉ ((syn_ccom (syn_c1st) (syn_c2nd))).fv :=
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
  have dv_cache_0017 : a ∉ ((syn_ccom (syn_c1st) (syn_c2nd))).fv :=
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
  have dv_cache_0018 : p ∉ ((syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))).fv :=
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
  have dv_cache_0019 : a ∉ ((syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))).fv :=
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
  have dv_cache_0025 : a ∉ ((Wff.classEq (.cv b) (syn_cop (.cv y) (.cv z)))).fv :=
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
  have dv_cache_0026 : p ∉ ((Wff.classEq (.cv b) (syn_cop (.cv y) (.cv a)))).fv :=
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
  have dv_cache_0027 : b ∉ ((syn_cop (.cv y) (.cv z))).fv :=
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
    b ∉ ((Wff.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))))).fv :=
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
      ((syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))).fv :=
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
  have dv_cache_0031 : p ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))).fv :=
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
      ((syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R))
          (.classMem (syn_cop (.cv x) (syn_cop B C)) R))).fv :=
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
      ((syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R))
          (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R))).fv :=
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
      ((Wff.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
          (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
            (.classMem (syn_cop A (syn_cop B C)) R)))).fv :=
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
  have p0000 := @g_elex (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)
  have p0001 := @g_opexb A (syn_cop B (syn_cop C D))
  have p0002 := @g_opexb B (syn_cop C D)
  have p0003 :=
    @g_anbi2i (.classMem (syn_cop B (syn_cop C D)) (syn_cvv))
      (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv)))
      (.classMem A (syn_cvv)) p0002
  have p0004 :=
    @g_bitri (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_cop B (syn_cop C D)) (syn_cvv)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv))))
      p0001 p0003
  have p0005 := @g_opexb C D
  have p0006 :=
    @g_simplbi (.classMem (syn_cop C D) (syn_cvv)) (.classMem C (syn_cvv))
      (.classMem D (syn_cvv)) p0005
  have p0007 :=
    @g_anim2i (.classMem (syn_cop C D) (syn_cvv)) (.classMem C (syn_cvv))
      (.classMem B (syn_cvv)) p0006
  have p0008 :=
    @g_anim2i (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem A (syn_cvv))
      p0007
  have p0009 :=
    @g_sylbi (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv))))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0004 p0008
  have p0010 :=
    @g_syl (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
      (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0000 p0009
  have p0011 := @g_elex (syn_cop A (syn_cop B C)) R
  have p0012 := @g_opexb A (syn_cop B C)
  have p0013 := @g_opexb B C
  have p0014 :=
    @g_anbi2i (.classMem (syn_cop B C) (syn_cvv))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem A (syn_cvv))
      p0013
  have p0015 :=
    @g_bitri (.classMem (syn_cop A (syn_cop B C)) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0012 p0014
  have p0016 :=
    @g_sylib (.classMem (syn_cop A (syn_cop B C)) R)
      (.classMem (syn_cop A (syn_cop B C)) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      p0011 p0015
  have p0017 := @g_opeq1 (.cv x) A (syn_cop B (syn_cop C D))
  have p0018 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B (syn_cop C D)))
      (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R) p0017
  have p0019 := @g_opeq1 (.cv x) A (syn_cop B C)
  have p0020 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B C))
      (syn_cop A (syn_cop B C)) R p0019
  have p0021 :=
    @g_bibi12d (.classEq (.cv x) A)
      (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R))
      (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
      (.classMem (syn_cop (.cv x) (syn_cop B C)) R)
      (.classMem (syn_cop A (syn_cop B C)) R) p0018 p0020
  have p0022 :=
    @g_imbi2d (.classEq (.cv x) A)
      (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R))
        (.classMem (syn_cop (.cv x) (syn_cop B C)) R))
      (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
        (.classMem (syn_cop A (syn_cop B C)) R))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0021
  have p0023 := @g_opeq1 (.cv y) B (syn_cop (.cv z) D)
  have p0024 :=
    @g_opeq2d (.classEq (.cv y) B) (syn_cop (.cv y) (syn_cop (.cv z) D))
      (syn_cop B (syn_cop (.cv z) D)) (.cv x) p0023
  have p0025 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
      (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R) p0024
  have p0026 := @g_opeq1 (.cv y) B (.cv z)
  have p0027 :=
    @g_opeq2d (.classEq (.cv y) B) (syn_cop (.cv y) (.cv z)) (syn_cop B (.cv z)) (.cv x)
      p0026
  have p0028 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))
      (syn_cop (.cv x) (syn_cop B (.cv z))) R p0027
  have p0029 :=
    @g_bibi12d (.classEq (.cv y) B)
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cins4 R))
      (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R))
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R)
      (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R) p0025 p0028
  have p0030 := @g_opeq1 (.cv z) C D
  have p0031 := @g_opeq2d (.classEq (.cv z) C) (syn_cop (.cv z) D) (syn_cop C D) B p0030
  have p0032 :=
    @g_opeq2d (.classEq (.cv z) C) (syn_cop B (syn_cop (.cv z) D))
      (syn_cop B (syn_cop C D)) (.cv x) p0031
  have p0033 :=
    @g_eleq1d (.classEq (.cv z) C) (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D)))
      (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R) p0032
  have p0034 := @g_opeq2 (.cv z) C B
  have p0035 :=
    @g_opeq2d (.classEq (.cv z) C) (syn_cop B (.cv z)) (syn_cop B C) (.cv x) p0034
  have p0036 :=
    @g_eleq1d (.classEq (.cv z) C) (syn_cop (.cv x) (syn_cop B (.cv z)))
      (syn_cop (.cv x) (syn_cop B C)) R p0035
  have p0037 :=
    @g_bibi12d (.classEq (.cv z) C)
      (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R))
      (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R))
      (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R)
      (.classMem (syn_cop (.cv x) (syn_cop B C)) R) p0033 p0036
  have p0038 := (Nominal.classEqRefl (syn_cins4 R))
  have p0039 :=
    @g_eleq2i (syn_cins4 R)
      (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R)
      (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) p0038
  have p0040 :=
    @g_brcnv (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
      (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))
  have p0041 :=
    @g_brtxp a b (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (.cv p)
      (syn_c1st)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
        (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0042 :=
    @g_n_3ancoma (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
  have p0043 :=
    @g_n_3anass
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
      (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
  have p0044 := @g_vex x
  have p0045 := @g_vex y
  have p0046 := @g_vex z
  have p0047 := @g_opex (.cv z) D p0046 hyp_oqelins4_4
  have p0048 := @g_opex (.cv y) (syn_cop (.cv z) D) p0045 p0047
  have p0049 :=
    @g_opbr1st (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)) (.cv a) p0044 p0048
  have p0050 := @g_equcom x a
  have p0051_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st)
          (.cv a)) (.objEq x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
    @g_bitri
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
      (.objEq x a) (.objEq a x) p0051_e00_recanon p0050
  have p0052 :=
    @g_anbi1i
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
      (.objEq a x)
      (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      p0051
  have p0053 :=
    @g_n_3bitri
      (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      (syn_w3a (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st)
          (.cv a)) (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      (syn_wa (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st)
          (.cv a)) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      (syn_wa (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      p0042 p0043 p0052
  have p0054 :=
    @g_exbii
      (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      (syn_wa (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      b p0053
  have p0055 :=
    @g_n_19_42v (.objEq a x)
      (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      b dv_cache_0010
  have p0056 :=
    @g_bitri
      (syn_wex b (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      (syn_wex b (syn_wa (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))
      (syn_wa (.objEq a x) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))
      p0054 p0055
  have p0057 :=
    @g_exbii
      (syn_wex b (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      (syn_wa (.objEq a x) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))
      a p0056
  have p0058 := @g_opeq1 (.cv a) (.cv x) (.cv b)
  have p0059_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a x) (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv x) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @g_eqeq2d (.objEq a x) (syn_cop (.cv a) (.cv b)) (syn_cop (.cv x) (.cv b)) (.cv p)
      p0059_e00_recanon
  have p0060 :=
    @g_anbi1d (.objEq a x) (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
      p0059
  have p0061 :=
    @g_exbidv (.objEq a x)
      (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      b dv_cache_0010 p0060
  have p0062_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv x)) (syn_wb (syn_wex b
            (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
              (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                  (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wex b
            (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
              (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                  (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_cphi syn_wbr syn_ctxp syn_cin syn_ccom syn_copab syn_ccnv syn_c1st
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
    @g_ceqsexv
      (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      a (.cv x) dv_cache_0011 dv_cache_0012 p0044 p0062_e01_recanon
  have p0063_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex a (syn_wa (.objEq a x) (syn_wex b
              (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
                (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                    (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))))
        (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))) :=
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
      p0062
  have p0063 :=
    @g_n_3bitri
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_c1st)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))) (.cv p))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))
      (syn_wex a (syn_wa (.objEq a x) (syn_wex b
            (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b)))
              (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                  (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))))
      (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      p0041 p0057 p0063_e02_recanon
  have p0064 :=
    @g_ancom (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
  have p0065 :=
    @g_brtxp p a (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (.cv b)
      (syn_ccom (syn_c1st) (syn_c2nd))
      (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) dv_cache_0013 dv_cache_0001
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020
  have p0066 :=
    @g_n_3anrot (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))
  have p0067 :=
    @g_brco2nd (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)) (.cv p) (syn_c1st) p0044
      p0048
  have p0068 := @g_opbr1st (.cv y) (syn_cop (.cv z) D) (.cv p) p0045 p0047
  have p0069 := @g_equcom y p
  have p0070_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_c1st) (.cv p))
        (.objEq y p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
    @g_n_3bitri
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
      (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_c1st) (.cv p)) (.objEq y p)
      (.objEq p y) p0067 p0070_e01_recanon p0069
  have p0071 :=
    @g_brco2nd (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)) (.cv a)
      (syn_ccom (syn_c1st) (syn_c2nd)) p0044 p0048
  have p0072 := @g_brco2nd (.cv y) (syn_cop (.cv z) D) (.cv a) (syn_c1st) p0045 p0047
  have p0073 := @g_opbr1st (.cv z) D (.cv a) p0046 hyp_oqelins4_4
  have p0074_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv z) D) (syn_c1st) (.cv a)) (.objEq z a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
    @g_bitri
      (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv a))
      (syn_wbr (syn_cop (.cv z) D) (syn_c1st) (.cv a)) (.objEq z a) p0072
      p0074_e01_recanon
  have p0075 := @g_equcom z a
  have p0076 :=
    @g_n_3bitri
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))
      (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv a))
      (.objEq z a) (.objEq a z) p0071 p0074 p0075
  have p0077 := @g_biid (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
  have p0078 :=
    @g_n_3anbi123i
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
      (.objEq p y)
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))
      (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
      (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) p0070 p0076 p0077
  have p0079 :=
    @g_bitri
      (syn_w3a (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a)))
      (syn_w3a (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))
        (.classEq (.cv b) (syn_cop (.cv p) (.cv a))))
      (syn_w3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a))))
      p0066 p0078
  have p0080 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a)))
      (syn_w3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))) p a
      p0079
  have p0081 := @g_opeq1 (.cv p) (.cv y) (.cv a)
  have p0082_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p y) (.classEq (syn_cop (.cv p) (.cv a)) (syn_cop (.cv y) (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0081
  have p0082 :=
    @g_eqeq2d (.objEq p y) (syn_cop (.cv p) (.cv a)) (syn_cop (.cv y) (.cv a)) (.cv b)
      p0082_e00_recanon
  have p0083 := @g_opeq2 (.cv a) (.cv z) (.cv y)
  have p0084_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a z) (.classEq (syn_cop (.cv y) (.cv a)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0083
  have p0084 :=
    @g_eqeq2d (.objEq a z) (syn_cop (.cv y) (.cv a)) (syn_cop (.cv y) (.cv z)) (.cv b)
      p0084_e00_recanon
  have p0085_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (.cv y)) (syn_wb (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
          (.classEq (.cv b) (syn_cop (.cv y) (.cv a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0082
  have p0085_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv z)) (syn_wb (.classEq (.cv b) (syn_cop (.cv y) (.cv a)))
          (.classEq (.cv b) (syn_cop (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0084
  have p0085 :=
    @g_ceqsex2v (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
      (.classEq (.cv b) (syn_cop (.cv y) (.cv a)))
      (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) p a (.cv y) (.cv z) dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0020
      p0045 p0046 p0085_e02_recanon p0085_e03_recanon
  have p0086_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex p (syn_wex a (syn_w3a (.objEq p y) (.objEq a z)
              (.classEq (.cv b) (syn_cop (.cv p) (.cv a))))))
        (.classEq (.cv b) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_cphi
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
    @g_n_3bitri
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
      (syn_wex p (syn_wex a (syn_w3a (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p))
            (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a)))))
      (syn_wex p (syn_wex a (syn_w3a (.objEq p y) (.objEq a z)
            (.classEq (.cv b) (syn_cop (.cv p) (.cv a))))))
      (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) p0065 p0080 p0086_e02_recanon
  have p0087 :=
    @g_anbi1i
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
        (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
      (.classEq (.cv b) (syn_cop (.cv y) (.cv z)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) p0086
  have p0088 :=
    @g_bitri
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      (syn_wa (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
        (.classEq (.cv p) (syn_cop (.cv x) (.cv b))))
      (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv z)))
        (.classEq (.cv p) (syn_cop (.cv x) (.cv b))))
      p0064 p0087
  have p0089 :=
    @g_exbii
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
        (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))
      (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv z)))
        (.classEq (.cv p) (syn_cop (.cv x) (.cv b))))
      b p0088
  have p0090 := @g_opex (.cv y) (.cv z) p0045 p0046
  have p0091 := @g_opeq2 (.cv b) (syn_cop (.cv y) (.cv z)) (.cv x)
  have p0092 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) (syn_cop (.cv x) (.cv b))
      (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) (.cv p) p0091
  have p0093 :=
    @g_ceqsexv (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
      (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) b
      (syn_cop (.cv y) (.cv z)) dv_cache_0027 dv_cache_0028 p0090 p0092
  have p0094 :=
    @g_bitri
      (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      (syn_wex b (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv z)))
          (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))))
      (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) p0089 p0093
  have p0095 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))
        (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))))
      (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_c1st)
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))) (.cv p))
      (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))
          (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))
      (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) p0040 p0063 p0094
  have p0096 :=
    @g_rexbii
      (syn_wbr (.cv p) (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))
        (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))))
      (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) p R p0095
  have p0097 :=
    @g_elima p (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))
      (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))
      R dv_cache_0013 dv_cache_0029 dv_cache_0030
  have p0098 :=
    @g_risset p (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R dv_cache_0031 dv_cache_0030
  have p0099 :=
    @g_n_3bitr4i
      (syn_wrex p R (syn_wbr (.cv p) (syn_ccnv (syn_ctxp (syn_c1st)
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))
          (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))))
      (syn_wrex p R (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))))
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cima (syn_ccnv
            (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R))
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R) p0096 p0097 p0098
  have p0100 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cins4 R))
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cima (syn_ccnv
            (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
                (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R))
      (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R) p0039 p0099
  have p0101 :=
    @g_vtocl2g
      (syn_wb (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cins4 R))
        (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R))
      (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R))
        (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R))
      (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R))
        (.classMem (syn_cop (.cv x) (syn_cop B C)) R))
      y z B C (syn_cvv) (syn_cvv) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 p0029 p0037 p0100
  have p0102 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R))
          (.classMem (syn_cop (.cv x) (syn_cop B C)) R)))
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
          (.classMem (syn_cop A (syn_cop B C)) R)))
      x A (syn_cvv) dv_cache_0037 dv_cache_0038 p0022 p0101
  have p0103 :=
    @g_imp (.classMem A (syn_cvv))
      (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
        (.classMem (syn_cop A (syn_cop B C)) R))
      p0102
  have p0104 :=
    @g_pm5_21nii (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))))
      (.classMem (syn_cop A (syn_cop B C)) R) p0010 p0016 p0103
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

@[expose]
noncomputable def g_ins2exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins2 A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cins2 A))
  have p0001 := @g_vvex
  have p0002 := @g_txpexg (syn_cvv) A (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cvv) (syn_cvv)) (.classMem A V)
      (.classMem (syn_ctxp (syn_cvv) A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_cins2 A) (syn_ctxp (syn_cvv) A) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_ins3exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins3 A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cins3 A))
  have p0001 := @g_vvex
  have p0002 := @g_txpexg A (syn_cvv) V (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_ctxp A (syn_cvv)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A V) (syn_cins3 A) (syn_ctxp A (syn_cvv)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_ins2ex (A : Class)
    (hyp_insex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins2 A) (syn_cvv)) :=
  by
  have p0000 := @g_ins2exg A (syn_cvv)
  have p0001 := Nominal.mp hyp_insex_1 p0000
  exact p0001

@[expose]
noncomputable def g_ins3ex (A : Class)
    (hyp_insex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins3 A) (syn_cvv)) :=
  by
  have p0000 := @g_ins3exg A (syn_cvv)
  have p0001 := Nominal.mp hyp_insex_1 p0000
  exact p0001

@[expose]
noncomputable def g_ins4ex (A : Class)
    (hyp_insex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins4 A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cins4 A))
  have p0001 := @g_n_1stex
  have p0003 := @g_n_2ndex
  have p0004 := @g_coex (syn_c1st) (syn_c2nd) p0001 p0003
  have p0006 := @g_coex (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd) p0004 p0003
  have p0007 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c2nd))
      (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) p0004 p0006
  have p0008 :=
    @g_txpex (syn_c1st)
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
        (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))
      p0001 p0007
  have p0009 :=
    @g_cnvex
      (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
          (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))
      p0008
  have p0010 :=
    @g_imaex
      (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
            (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))
      A p0009 hyp_insex_1
  have p0011 :=
    @g_eqeltri (syn_cins4 A)
      (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd))
              (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) A)
      (syn_cvv) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_imageexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cimage A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cimage A))
  have p0001 := @g_siexg A V
  have p0002 := @g_cnvexg (syn_csi A) (syn_cvv)
  have p0003 := @g_ssetex
  have p0004 := @g_coexg (syn_csset) (syn_ccnv (syn_csi A)) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_mpan (.classMem (syn_csset) (syn_cvv)) (.classMem (syn_ccnv (syn_csi A)) (syn_cvv))
      (.classMem (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_n_3syl (.classMem A V) (.classMem (syn_csi A) (syn_cvv))
      (.classMem (syn_ccnv (syn_csi A)) (syn_cvv))
      (.classMem (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) p0001 p0002
      p0005
  have p0007 := @g_ins3exg (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)
  have p0009 := @g_ins2ex (syn_csset) p0003
  have p0010 :=
    @g_symdifexg (syn_cins2 (syn_csset))
      (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_mpan (.classMem (syn_cins2 (syn_csset)) (syn_cvv))
      (.classMem (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cvv))
      (.classMem (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv))
      p0009 p0010
  have p0012 :=
    @g_n_3syl (.classMem A V)
      (.classMem (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv))
      (.classMem (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cvv))
      (.classMem (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv))
      p0006 p0007 p0011
  have p0013 := @g_n_1cex
  have p0014 :=
    @g_imaexg
      (syn_csymdif (syn_cins2 (syn_csset))
        (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))
      (syn_c1c) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_mpan2
      (.classMem (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv))
      (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)) (syn_cvv))
      p0013 p0014
  have p0016 :=
    @g_complexg
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c))
      (syn_cvv)
  have p0017 :=
    @g_n_3syl (.classMem A V)
      (.classMem (syn_csymdif (syn_cins2 (syn_csset))
          (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cvv))
      (.classMem (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)) (syn_cvv))
      (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
              (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c))) (syn_cvv))
      p0012 p0015 p0016
  have p0018 :=
    @g_syl5eqel (.classMem A V) (syn_cimage A)
      (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)))
      (syn_cvv) p0000 p0017
  exact p0018

@[expose]
noncomputable def g_imageex (A : Class)
    (hyp_imageex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cimage A) (syn_cvv)) :=
  by
  have p0000 := @g_imageexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_imageex_1 p0000
  exact p0001

@[expose]
noncomputable def g_dmtxp (R : Class) (S : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_ctxp R S)) (syn_cin (syn_cdm R) (syn_cdm S))) :=
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
    p ∉ ((syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))).fv :=
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
  have dv_cache_0011 : p ∉ ((syn_cop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0013 : p ∉ ((syn_ctxp R S)).fv :=
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
  have dv_cache_0014 : z ∉ ((syn_wbr (.cv x) R (.cv y))).fv :=
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
  have dv_cache_0015 : y ∉ ((syn_wbr (.cv x) S (.cv z))).fv :=
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
  have dv_cache_0016 : x ∉ ((syn_cdm (syn_ctxp R S))).fv :=
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
  have dv_cache_0017 : x ∉ ((syn_cin (syn_cdm R) (syn_cdm S))).fv :=
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
    @g_brtxp y z (.cv x) (.cv p) R S dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @g_exbii (syn_wbr (.cv x) (syn_ctxp R S) (.cv p))
      (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
            (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      p p0000
  have p0002 :=
    @g_exrot3
      (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y))
        (syn_wbr (.cv x) S (.cv z)))
      p y z
  have p0003 :=
    @g_bitri (syn_wex p (syn_wbr (.cv x) (syn_ctxp R S) (.cv p)))
      (syn_wex p (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
              (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))))
      (syn_wex y (syn_wex z (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
              (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))))
      p0001 p0002
  have p0004 :=
    @g_n_3anass (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y))
      (syn_wbr (.cv x) S (.cv z))
  have p0005 :=
    @g_exbii
      (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y))
        (syn_wbr (.cv x) S (.cv z)))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))
      p p0004
  have p0006 :=
    @g_n_19_41v (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p dv_cache_0010
  have p0007 :=
    @g_bitri
      (syn_wex p
        (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (.cv x) S (.cv z))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
          (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      (syn_wa (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z))))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))
      p0005 p0006
  have p0008 := @g_vex y
  have p0009 := @g_vex z
  have p0010 := @g_opex (.cv y) (.cv z) p0008 p0009
  have p0011 := @g_isseti p (syn_cop (.cv y) (.cv z)) dv_cache_0011 p0010
  have p0012 :=
    @g_biantrur (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p0011
  have p0013 :=
    @g_bicomi (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))
      (syn_wa (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z))))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))
      p0012
  have p0014 :=
    @g_bitri
      (syn_wex p
        (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (.cv x) S (.cv z))))
      (syn_wa (syn_wex p (.classEq (.cv p) (syn_cop (.cv y) (.cv z))))
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) p0007 p0013
  have p0015 :=
    @g_n_2exbii
      (syn_wex p
        (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z))) (syn_wbr (.cv x) R (.cv y))
          (syn_wbr (.cv x) S (.cv z))))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))) y z p0014
  have p0016 :=
    @g_bitri (syn_wex p (syn_wbr (.cv x) (syn_ctxp R S) (.cv p)))
      (syn_wex y (syn_wex z (syn_wex p (syn_w3a (.classEq (.cv p) (syn_cop (.cv y) (.cv z)))
              (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z))))))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      p0003 p0015
  have p0017 := @g_eldm p (.cv x) (syn_ctxp R S) dv_cache_0012 dv_cache_0013
  have p0018 := @g_elin (.cv x) (syn_cdm R) (syn_cdm S)
  have p0019 := @g_eldm y (.cv x) R dv_cache_0001 dv_cache_0005
  have p0020 := @g_eldm z (.cv x) S dv_cache_0002 dv_cache_0008
  have p0021 :=
    @g_anbi12i (.classMem (.cv x) (syn_cdm R)) (syn_wex y (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) (syn_cdm S)) (syn_wex z (syn_wbr (.cv x) S (.cv z))) p0019 p0020
  have p0022 :=
    @g_eeanv (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)) y z dv_cache_0014
      dv_cache_0015
  have p0023 :=
    @g_bicomi
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      (syn_wa (syn_wex y (syn_wbr (.cv x) R (.cv y))) (syn_wex z (syn_wbr (.cv x) S (.cv z))))
      p0022
  have p0024 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cdm R)) (.classMem (.cv x) (syn_cdm S)))
      (syn_wa (syn_wex y (syn_wbr (.cv x) R (.cv y))) (syn_wex z (syn_wbr (.cv x) S (.cv z))))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      p0021 p0023
  have p0025 :=
    @g_bitri (.classMem (.cv x) (syn_cin (syn_cdm R) (syn_cdm S)))
      (syn_wa (.classMem (.cv x) (syn_cdm R)) (.classMem (.cv x) (syn_cdm S)))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      p0018 p0024
  have p0026 :=
    @g_n_3bitr4i (syn_wex p (syn_wbr (.cv x) (syn_ctxp R S) (.cv p)))
      (syn_wex y (syn_wex z (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) S (.cv z)))))
      (.classMem (.cv x) (syn_cdm (syn_ctxp R S)))
      (.classMem (.cv x) (syn_cin (syn_cdm R) (syn_cdm S))) p0016 p0017 p0025
  have p0027 :=
    @g_eqriv x (syn_cdm (syn_ctxp R S)) (syn_cin (syn_cdm R) (syn_cdm S)) dv_cache_0016
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

@[expose]
noncomputable def g_fntxp (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_ctxp F G) (syn_cin A B))) :=
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
      ((syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv x) F (.cv a))
          (syn_wbr (.cv x) G (.cv b)))).fv :=
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
      ((syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv x) F (.cv a))
          (syn_wbr (.cv x) G (.cv b)))).fv :=
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
      ((syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wbr (.cv x) F (.cv c))
          (syn_wbr (.cv x) G (.cv d)))).fv :=
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
      ((syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wbr (.cv x) F (.cv c))
          (syn_wbr (.cv x) G (.cv d)))).fv :=
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
  have dv_cache_0027 : c ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0028 : d ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0031 : a ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0032 : b ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0033 : z ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0034 : x ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0035 : y ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have dv_cache_0036 : x ∉ ((syn_ctxp F G)).fv :=
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
  have dv_cache_0037 : y ∉ ((syn_ctxp F G)).fv :=
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
  have dv_cache_0038 : z ∉ ((syn_ctxp F G)).fv :=
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
    @g_brtxp a b (.cv x) (.cv y) F G dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0001 :=
    @g_brtxp c d (.cv x) (.cv z) F G dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0002 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ctxp F G) (.cv y))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
            (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) G (.cv b)))))
      (syn_wbr (.cv x) (syn_ctxp F G) (.cv z))
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
            (syn_wbr (.cv x) F (.cv c)) (syn_wbr (.cv x) G (.cv d)))))
      p0000 p0001
  have p0003 :=
    @g_ee4anv
      (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv x) F (.cv a))
        (syn_wbr (.cv x) G (.cv b)))
      (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wbr (.cv x) F (.cv c))
        (syn_wbr (.cv x) G (.cv d)))
      a b c d dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
  have p0004 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) (syn_ctxp F G) (.cv y)) (syn_wbr (.cv x) (syn_ctxp F G) (.cv z)))
      (syn_wa (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
              (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) G (.cv b))))) (syn_wex c (syn_wex d
            (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
              (syn_wbr (.cv x) F (.cv c)) (syn_wbr (.cv x) G (.cv d))))))
      (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_wa
                (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
                  (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) G (.cv b)))
                (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
                  (syn_wbr (.cv x) F (.cv c)) (syn_wbr (.cv x) G (.cv d))))))))
      p0002 p0003
  have p0005 :=
    @g_an6 (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv x) F (.cv a))
      (syn_wbr (.cv x) G (.cv b)) (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
      (syn_wbr (.cv x) F (.cv c)) (syn_wbr (.cv x) G (.cv d))
  have p0006 := @g_fununiq (.cv x) (.cv a) (.cv c) F
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun F) (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
        (.objEq a c)) :=
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
      p0006
  have p0007 :=
    @g_n_3expib (syn_wfun F) (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c))
      (.objEq a c) p0007_e00_recanon
  have p0008 := @g_fununiq (.cv x) (.cv b) (.cv d) G
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun G) (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d)))
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
      p0008
  have p0009 :=
    @g_n_3expib (syn_wfun G) (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d))
      (.objEq b d) p0009_e00_recanon
  have p0010 :=
    @g_im2anan9 (syn_wfun F)
      (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c))) (.objEq a c)
      (syn_wfun G) (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d)))
      (.objEq b d) p0007 p0009
  have p0011 :=
    @g_eqeq12 (.cv y) (syn_cop (.cv a) (.cv b)) (.cv z) (syn_cop (.cv c) (.cv d))
  have p0012 := @g_opth (.cv a) (.cv b) (.cv c) (.cv d)
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
          (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))) (syn_wb (.objEq y z)
          (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv c) (.cv d))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex
          syn_cphi syn_wb
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
      (syn_wb (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv c) (.cv d)))
        (syn_wa (.objEq a c) (.objEq b d))) :=
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
    @g_syl6bb
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (.objEq y z) (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv c) (.cv d)))
      (syn_wa (.objEq a c) (.objEq b d)) p0013_e00_recanon p0013_e01_recanon
  have p0014 :=
    @g_imbi2d
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (.objEq y z) (syn_wa (.objEq a c) (.objEq b d))
      (syn_wa (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
        (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d))))
      p0013
  have p0015 :=
    @g_syl5ibrcom (syn_wa (syn_wfun F) (syn_wfun G))
      (.imp (syn_wa (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
          (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d)))) (.objEq y z))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (.imp (syn_wa (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
          (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d))))
        (syn_wa (.objEq a c) (.objEq b d)))
      p0010 p0014
  have p0016 :=
    @g_exp4a (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
      (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d))) (.objEq y z) p0015
  have p0017 :=
    @g_n_3impd (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
      (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d))) (.objEq y z) p0016
  have p0018 :=
    @g_syl5bi
      (syn_wa (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv x) F (.cv a))
          (syn_wbr (.cv x) G (.cv b)))
        (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wbr (.cv x) F (.cv c))
          (syn_wbr (.cv x) G (.cv d))))
      (syn_w3a (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
          (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
        (syn_wa (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) F (.cv c)))
        (syn_wa (syn_wbr (.cv x) G (.cv b)) (syn_wbr (.cv x) G (.cv d))))
      (syn_wa (syn_wfun F) (syn_wfun G)) (.objEq y z) p0005 p0017
  have p0019 :=
    @g_exlimdvv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wa (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv x) F (.cv a))
          (syn_wbr (.cv x) G (.cv b)))
        (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wbr (.cv x) F (.cv c))
          (syn_wbr (.cv x) G (.cv d))))
      (.objEq y z) c d dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 p0018
  have p0020 :=
    @g_exlimdvv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wex c (syn_wex d (syn_wa (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
              (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) G (.cv b)))
            (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
              (syn_wbr (.cv x) F (.cv c)) (syn_wbr (.cv x) G (.cv d))))))
      (.objEq y z) a b dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0019
  have p0021 :=
    @g_syl5bi
      (syn_wa (syn_wbr (.cv x) (syn_ctxp F G) (.cv y)) (syn_wbr (.cv x) (syn_ctxp F G) (.cv z)))
      (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_wa
                (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
                  (syn_wbr (.cv x) F (.cv a)) (syn_wbr (.cv x) G (.cv b)))
                (syn_w3a (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
                  (syn_wbr (.cv x) F (.cv c)) (syn_wbr (.cv x) G (.cv d))))))))
      (syn_wa (syn_wfun F) (syn_wfun G)) (.objEq y z) p0004 p0020
  have p0022 :=
    @g_alrimiv (syn_wa (syn_wfun F) (syn_wfun G))
      (.imp (syn_wa (syn_wbr (.cv x) (syn_ctxp F G) (.cv y))
          (syn_wbr (.cv x) (syn_ctxp F G) (.cv z))) (.objEq y z))
      z dv_cache_0033 p0021
  have p0023 :=
    @g_alrimivv (syn_wa (syn_wfun F) (syn_wfun G))
      (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ctxp F G) (.cv y))
            (syn_wbr (.cv x) (syn_ctxp F G) (.cv z))) (.objEq y z)))
      x y dv_cache_0034 dv_cache_0035 p0022
  have p0024 :=
    @g_dffun2 x y z (syn_ctxp F G) dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
      dv_cache_0040 dv_cache_0041
  have p0025 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wfun G))
      (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ctxp F G) (.cv y))
                (syn_wbr (.cv x) (syn_ctxp F G) (.cv z))) (.objEq y z)))))
      (syn_wfun (syn_ctxp F G)) p0023 p0024
  have p0026 := @g_dmtxp F G
  have p0027 := @g_ineq12 (syn_cdm F) A (syn_cdm G) B
  have p0028 :=
    @g_syl5eq (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_cdm (syn_ctxp F G)) (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin A B) p0026 p0027
  have p0029 :=
    @g_anim12i (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wfun (syn_ctxp F G))
      (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (.classEq (syn_cdm (syn_ctxp F G)) (syn_cin A B)) p0025 p0028
  have p0030 :=
    @g_an4s (syn_wfun F) (syn_wfun G) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)
      (syn_wa (syn_wfun (syn_ctxp F G)) (.classEq (syn_cdm (syn_ctxp F G)) (syn_cin A B)))
      p0029
  have p0031 := (Nominal.biimpRefl (syn_wfn F A))
  have p0032 := (Nominal.biimpRefl (syn_wfn G B))
  have p0033 :=
    @g_anbi12i (syn_wfn F A) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A)) (syn_wfn G B)
      (syn_wa (syn_wfun G) (.classEq (syn_cdm G) B)) p0031 p0032
  have p0034 := (Nominal.biimpRefl (syn_wfn (syn_ctxp F G) (syn_cin A B)))
  have p0035 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A))
        (syn_wa (syn_wfun G) (.classEq (syn_cdm G) B)))
      (syn_wa (syn_wfun (syn_ctxp F G)) (.classEq (syn_cdm (syn_ctxp F G)) (syn_cin A B)))
      (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_ctxp F G) (syn_cin A B)) p0030
      p0033 p0034
  exact p0035


end NFChoice.DirectNominalPrf.WPPReplay

end
