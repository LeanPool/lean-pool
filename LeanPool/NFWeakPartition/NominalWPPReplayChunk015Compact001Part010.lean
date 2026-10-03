/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk015Compact001Block002

/-! NF weak partition development: NominalWPPReplayChunk015Compact001Part010. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnqordantisym (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have fresh_v_ne_t : v ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_v : t ≠ v := Ne.symm fresh_v_ne_t
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : Disjoint (C).fv ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (C).fv ((Class.cv x)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ x } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show x ∉ (C).fv from (by exact fresh_x_not_C))))))
  have dv_cache_0003 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0004 : Disjoint ((Class.cv x)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0005 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0006 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint (C).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (C).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (C).fv from (by exact fresh_y_not_C))))))
  have dv_cache_0008 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0009 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0010 : v ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_y, not_false_eq_true])
  have dv_cache_0011 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((syn_cec (.cv u) (syn_clnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_u, fresh_t_not_R, or_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((syn_cec (.cv v) (syn_clnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_v, fresh_t_not_R, or_false, not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
                (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C)
            (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_C, fresh_t_not_R,
          fresh_t_ne_u, fresh_t_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : v ∉ ((Wff.classEq (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, or_false, not_false_eq_true])
  have dv_cache_0016 :
    v ∉
      ((syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_not_C, fresh_v_not_R,
          fresh_v_ne_u, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ ((Wff.classEq (.cv x) (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, or_false, not_false_eq_true])
  have dv_cache_0018 :
    u ∉
      ((syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_C, fresh_u_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((syn_clnquo R C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((syn_clnquo R C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((syn_clnqord R C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ ((syn_clnqord R C)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0023 :
    x ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0024 :
    y ∉
      ((syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0025 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0001 := @g_lnqordexg C R dv_cache_0001
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnqord R C) (syn_cvv)) p0000 p0001
  have p0004 := @g_lnquoexg C R dv_cache_0001
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnquo R C) (syn_cvv)) p0000 p0004
  have p0006 :=
    @g_simp2
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0007 :=
    @g_simpl (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0008 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (.classMem (.cv x) (syn_clnquo R C)) p0006 p0007
  have p0009 := @g_vex x
  have p0010 :=
    @g_ellnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0009
  have p0011 :=
    @g_biimpi (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0010
  have p0012 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (.classMem (.cv x) (syn_clnquo R C))
      (syn_wrex u C (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))) p0008 p0011
  have p0013 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0014 :=
    @g_simp2
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0015 :=
    @g_simpr (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C))
  have p0016 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (.classMem (.cv y) (syn_clnquo R C)) p0014 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (.classMem (.cv y) (syn_clnquo R C)) p0013 p0016
  have p0018 := @g_vex y
  have p0019 :=
    @g_ellnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0018
  have p0020 :=
    @g_biimpi (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0019
  have p0021 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0017 p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0023 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0024 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0025 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0026 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0024 p0025
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0023 p0026
  have p0028 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0029 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0028 p0029
  have p0031 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0030 p0031
  have p0033 := @g_simpr (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_ctrans) C) p0032 p0033
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_ctrans) C) p0027 p0034
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr R (syn_ctrans) C) p0022 p0035
  have p0037 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0038 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0039 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0038 p0039
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) p0037 p0040
  have p0042 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0043 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0044 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0045 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0046 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0044 p0045
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0043 p0046
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) p0042 p0047
  have p0049 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0050 := @g_ellnkerecg (.cv t) (.cv u) R
  have p0051 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0050
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0049 p0051
  have p0053 := @g_simpl (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u)))
      (syn_wbr (.cv u) R (.cv t)) p0052 p0053
  have p0055 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0056 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0057 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0058 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0059 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0057 p0058
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0056 p0059
  have p0061 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0062 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0061 p0062
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0060 p0063
  have p0065 :=
    @g_ssbrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      R (syn_cxp C C) (.cv u) (.cv t) p0064
  have p0066 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.imp (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv u) (syn_cxp C C) (.cv t))) p0055
      p0065
  have p0067 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv u) (syn_cxp C C) (.cv t)) p0054 p0066
  have p0068 := @g_brxp (.cv u) (.cv t) C C
  have p0069 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv u) (syn_cxp C C) (.cv t))
        (syn_wa (.classMem (.cv u) C) (.classMem (.cv t) C)))
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      p0068
  have p0070 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wbr (.cv u) (syn_cxp C C) (.cv t))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv t) C)) p0067 p0069
  have p0071 := @g_simpr (.classMem (.cv u) C) (.classMem (.cv t) C)
  have p0072 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0070
      p0071
  have p0073 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0074 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0075 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      p0074 p0075
  have p0077 :=
    @g_simp3
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0078 :=
    @g_simpr (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
  have p0079 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) p0077 p0078
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) p0076 p0079
  have p0081 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0082 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0081 p0082
  have p0084 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0085 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0086 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0087 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0085 p0086
  have p0088 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0084 p0087
  have p0089 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0083 p0088
  have p0090 :=
    @g_breq12 (.cv y) (syn_cec (.cv v) (syn_clnker R)) (.cv x)
      (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
        (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))))
      p0089 p0090
  have p0092 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0093 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0094 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0095 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0093 p0094
  have p0096 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0092 p0095
  have p0097 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0098 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0099 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0097 p0098
  have p0100 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0096 p0099
  have p0101 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0102 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0103 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0104 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0102 p0103
  have p0105 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0101 p0104
  have p0106 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0107 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0108 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0106 p0107
  have p0109 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0110 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0108 p0109
  have p0111 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0105 p0110
  have p0112 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0113 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0114 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0115 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0113 p0114
  have p0116 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0112 p0115
  have p0117 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0118 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0119 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0117 p0118
  have p0120 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0116 p0119
  have p0121 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0111 p0120
  have p0122 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0123 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0124 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0122 p0123
  have p0125 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0126 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0127 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0128 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0126 p0127
  have p0129 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0125 p0128
  have p0130 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv u) C) p0124 p0129
  have p0131 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0121 p0130
  have p0132 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      p0100 p0131
  have p0133 := @g_brlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0134 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C))))
      (syn_wb (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv v) R (.cv u)))
      p0132 p0133
  have p0135 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
      (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv v) R (.cv u)) p0091 p0134
  have p0136 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) (syn_wbr (.cv v) R (.cv u)) p0080 p0135
  have p0137 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv v) R (.cv u)) p0073 p0136
  have p0138 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0139 := @g_ellnkerecg (.cv t) (.cv u) R
  have p0140 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0139
  have p0141 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0138 p0140
  have p0142 := @g_simpl (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))
  have p0143 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u)))
      (syn_wbr (.cv u) R (.cv t)) p0141 p0142
  have p0144 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      C R (.cv v) (.cv u) (.cv t) p0036 p0041 p0048 p0072 p0137 p0143
  have p0145 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0146 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0147 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0148 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0149 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0147 p0148
  have p0150 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0146 p0149
  have p0151 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0152 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0153 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0151 p0152
  have p0154 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0155 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0153 p0154
  have p0156 := @g_simpr (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0157 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_ctrans) C) p0155 p0156
  have p0158 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_ctrans) C) p0150 p0157
  have p0159 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr R (syn_ctrans) C) p0145 p0158
  have p0160 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0161 := @g_ellnkerecg (.cv t) (.cv u) R
  have p0162 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0161
  have p0163 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0160 p0162
  have p0164 := @g_simpl (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))
  have p0165 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u)))
      (syn_wbr (.cv u) R (.cv t)) p0163 p0164
  have p0166 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0167 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0168 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0169 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0170 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0168 p0169
  have p0171 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0167 p0170
  have p0172 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0173 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0174 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0172 p0173
  have p0175 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0171 p0174
  have p0176 :=
    @g_ssbrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      R (syn_cxp C C) (.cv u) (.cv t) p0175
  have p0177 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.imp (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv u) (syn_cxp C C) (.cv t))) p0166
      p0176
  have p0178 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv u) (syn_cxp C C) (.cv t)) p0165 p0177
  have p0179 := @g_brxp (.cv u) (.cv t) C C
  have p0180 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv u) (syn_cxp C C) (.cv t))
        (syn_wa (.classMem (.cv u) C) (.classMem (.cv t) C)))
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      p0179
  have p0181 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wbr (.cv u) (syn_cxp C C) (.cv t))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv t) C)) p0178 p0180
  have p0182 := @g_simpr (.classMem (.cv u) C) (.classMem (.cv t) C)
  have p0183 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0181
      p0182
  have p0184 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0185 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0186 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0187 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0188 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0186 p0187
  have p0189 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0185 p0188
  have p0190 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) p0184 p0189
  have p0191 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0192 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0193 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0194 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0192 p0193
  have p0195 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) p0191 p0194
  have p0196 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0197 := @g_ellnkerecg (.cv t) (.cv u) R
  have p0198 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0197
  have p0199 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0196 p0198
  have p0200 := @g_simpr (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))
  have p0201 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u)))
      (syn_wbr (.cv t) R (.cv u)) p0199 p0200
  have p0202 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
  have p0203 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0204 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0205 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      p0203 p0204
  have p0206 :=
    @g_simp3
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0207 :=
    @g_simpl (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
  have p0208 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) p0206 p0207
  have p0209 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) p0205 p0208
  have p0210 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0211 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0212 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0213 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0211 p0212
  have p0214 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0210 p0213
  have p0215 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0216 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0217 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0215 p0216
  have p0218 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0214 p0217
  have p0219 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv y)
      (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
  have p0220 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
        (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))))
      p0218 p0219
  have p0221 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0222 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0223 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0224 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0222 p0223
  have p0225 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0221 p0224
  have p0226 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0227 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0228 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0226 p0227
  have p0229 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0225 p0228
  have p0230 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0231 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0232 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0233 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0231 p0232
  have p0234 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0230 p0233
  have p0235 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0236 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0237 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0235 p0236
  have p0238 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0239 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0237 p0238
  have p0240 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0234 p0239
  have p0241 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0242 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0243 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0244 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0242 p0243
  have p0245 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0241 p0244
  have p0246 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0247 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0248 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0246 p0247
  have p0249 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0245 p0248
  have p0250 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0240 p0249
  have p0251 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0252 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0253 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0254 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0252 p0253
  have p0255 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0251 p0254
  have p0256 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0257 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0258 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0256 p0257
  have p0259 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0255 p0258
  have p0260 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0250 p0259
  have p0261 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0229 p0260
  have p0262 := @g_brlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0263 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))) (syn_wbr (.cv u) R (.cv v)))
      p0261 p0262
  have p0264 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv v) (syn_clnker R)))
      (syn_wbr (.cv u) R (.cv v)) p0220 p0263
  have p0265 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv u) R (.cv v)) p0209 p0264
  have p0266 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v)) p0202 p0265
  have p0267 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      C R (.cv t) (.cv u) (.cv v) p0159 p0183 p0190 p0195 p0201 p0266
  have p0268 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v)) p0144 p0267
  have p0269 := @g_ellnkerecg (.cv t) (.cv v) R
  have p0270 :=
    @g_a1i
      (syn_wb (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
        (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))))
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      p0269
  have p0271 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0268 p0270
  have p0272 :=
    @g_ex
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))) p0271
  have p0273 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0274 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0275 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0276 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0277 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0275 p0276
  have p0278 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0274 p0277
  have p0279 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0280 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0281 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0279 p0280
  have p0282 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0283 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0281 p0282
  have p0284 := @g_simpr (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0285 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_ctrans) C) p0283 p0284
  have p0286 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_ctrans) C) p0278 p0285
  have p0287 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr R (syn_ctrans) C) p0273 p0286
  have p0288 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0289 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0290 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0291 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0292 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0290 p0291
  have p0293 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0289 p0292
  have p0294 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) p0288 p0293
  have p0295 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0296 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0297 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0298 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0296 p0297
  have p0299 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) p0295 p0298
  have p0300 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0301 := @g_ellnkerecg (.cv t) (.cv v) R
  have p0302 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0301
  have p0303 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0300 p0302
  have p0304 := @g_simpl (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))
  have p0305 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v)))
      (syn_wbr (.cv v) R (.cv t)) p0303 p0304
  have p0306 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0307 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0308 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0309 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0310 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0308 p0309
  have p0311 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0307 p0310
  have p0312 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0313 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0314 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0312 p0313
  have p0315 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0311 p0314
  have p0316 :=
    @g_ssbrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      R (syn_cxp C C) (.cv v) (.cv t) p0315
  have p0317 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.imp (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv v) (syn_cxp C C) (.cv t))) p0306
      p0316
  have p0318 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv v) (syn_cxp C C) (.cv t)) p0305 p0317
  have p0319 := @g_brxp (.cv v) (.cv t) C C
  have p0320 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv v) (syn_cxp C C) (.cv t))
        (syn_wa (.classMem (.cv v) C) (.classMem (.cv t) C)))
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      p0319
  have p0321 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wbr (.cv v) (syn_cxp C C) (.cv t))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv t) C)) p0318 p0320
  have p0322 := @g_simpr (.classMem (.cv v) C) (.classMem (.cv t) C)
  have p0323 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0321
      p0322
  have p0324 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0325 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0326 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0327 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      p0325 p0326
  have p0328 :=
    @g_simp3
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0329 :=
    @g_simpl (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
  have p0330 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) p0328 p0329
  have p0331 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) p0327 p0330
  have p0332 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0333 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0334 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0335 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0333 p0334
  have p0336 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0332 p0335
  have p0337 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0338 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0339 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0337 p0338
  have p0340 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0336 p0339
  have p0341 :=
    @g_breq12 (.cv x) (syn_cec (.cv u) (syn_clnker R)) (.cv y)
      (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
  have p0342 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
        (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))))
      p0340 p0341
  have p0343 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0344 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0345 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0346 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0344 p0345
  have p0347 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0343 p0346
  have p0348 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0349 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0350 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0348 p0349
  have p0351 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0347 p0350
  have p0352 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0353 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0354 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0355 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0353 p0354
  have p0356 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0352 p0355
  have p0357 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0358 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0359 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0357 p0358
  have p0360 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0361 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0359 p0360
  have p0362 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0356 p0361
  have p0363 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0364 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0365 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0366 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0364 p0365
  have p0367 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0363 p0366
  have p0368 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0369 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0370 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0368 p0369
  have p0371 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0367 p0370
  have p0372 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0362 p0371
  have p0373 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0374 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0375 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0376 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0374 p0375
  have p0377 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0373 p0376
  have p0378 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0379 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0380 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0378 p0379
  have p0381 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0377 p0380
  have p0382 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0372 p0381
  have p0383 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0351 p0382
  have p0384 := @g_brlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0385 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv v) (syn_clnker R))) (syn_wbr (.cv u) R (.cv v)))
      p0383 p0384
  have p0386 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv v) (syn_clnker R)))
      (syn_wbr (.cv u) R (.cv v)) p0342 p0385
  have p0387 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv x) (syn_clnqord R C) (.cv y)) (syn_wbr (.cv u) R (.cv v)) p0331 p0386
  have p0388 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv u) R (.cv v)) p0324 p0387
  have p0389 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0390 := @g_ellnkerecg (.cv t) (.cv v) R
  have p0391 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0390
  have p0392 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0389 p0391
  have p0393 := @g_simpl (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))
  have p0394 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v)))
      (syn_wbr (.cv v) R (.cv t)) p0392 p0393
  have p0395 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      C R (.cv u) (.cv v) (.cv t) p0287 p0294 p0299 p0323 p0388 p0394
  have p0396 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0397 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0398 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0399 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0400 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0398 p0399
  have p0401 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0397 p0400
  have p0402 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0403 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0404 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0402 p0403
  have p0405 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0406 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0404 p0405
  have p0407 := @g_simpr (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0408 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_ctrans) C) p0406 p0407
  have p0409 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr R (syn_ctrans) C) p0401 p0408
  have p0410 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr R (syn_ctrans) C) p0396 p0409
  have p0411 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0412 := @g_ellnkerecg (.cv t) (.cv v) R
  have p0413 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0412
  have p0414 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0411 p0413
  have p0415 := @g_simpl (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))
  have p0416 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v)))
      (syn_wbr (.cv v) R (.cv t)) p0414 p0415
  have p0417 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0418 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0419 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0420 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0421 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0419 p0420
  have p0422 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0418 p0421
  have p0423 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0424 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0425 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0423 p0424
  have p0426 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0422 p0425
  have p0427 :=
    @g_ssbrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      R (syn_cxp C C) (.cv v) (.cv t) p0426
  have p0428 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.imp (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv v) (syn_cxp C C) (.cv t))) p0417
      p0427
  have p0429 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv v) (syn_cxp C C) (.cv t)) p0416 p0428
  have p0430 := @g_brxp (.cv v) (.cv t) C C
  have p0431 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv v) (syn_cxp C C) (.cv t))
        (syn_wa (.classMem (.cv v) C) (.classMem (.cv t) C)))
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      p0430
  have p0432 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wbr (.cv v) (syn_cxp C C) (.cv t))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv t) C)) p0429 p0431
  have p0433 := @g_simpr (.classMem (.cv v) C) (.classMem (.cv t) C)
  have p0434 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0432
      p0433
  have p0435 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0436 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0437 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0438 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0436 p0437
  have p0439 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) p0435 p0438
  have p0440 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0441 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0442 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0443 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0444 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0442 p0443
  have p0445 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0441 p0444
  have p0446 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv u) C) p0440 p0445
  have p0447 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0448 := @g_ellnkerecg (.cv t) (.cv v) R
  have p0449 :=
    @g_biimpi (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0448
  have p0450 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))) p0447 p0449
  have p0451 := @g_simpr (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v))
  have p0452 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wbr (.cv v) R (.cv t)) (syn_wbr (.cv t) R (.cv v)))
      (syn_wbr (.cv t) R (.cv v)) p0450 p0451
  have p0453 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
  have p0454 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0455 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0456 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      p0454 p0455
  have p0457 :=
    @g_simp3
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0458 :=
    @g_simpr (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
  have p0459 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) p0457 p0458
  have p0460 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) p0456 p0459
  have p0461 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0462 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0463 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0461 p0462
  have p0464 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0465 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0466 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0467 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0465 p0466
  have p0468 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0464 p0467
  have p0469 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0463 p0468
  have p0470 :=
    @g_breq12 (.cv y) (syn_cec (.cv v) (syn_clnker R)) (.cv x)
      (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C)
  have p0471 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (syn_wb (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
        (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))))
      p0469 p0470
  have p0472 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0473 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0474 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0475 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0473 p0474
  have p0476 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0472 p0475
  have p0477 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0478 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0479 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0477 p0478
  have p0480 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (.classMem R (syn_cvv)) p0476 p0479
  have p0481 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0482 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0483 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0484 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0482 p0483
  have p0485 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0481 p0484
  have p0486 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0487 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0488 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0486 p0487
  have p0489 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0490 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0488 p0489
  have p0491 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0485 p0490
  have p0492 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0493 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0494 :=
    @g_simp1
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
      (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
        (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))
  have p0495 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0493 p0494
  have p0496 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0492 p0495
  have p0497 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0498 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0499 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0497 p0498
  have p0500 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0496 p0499
  have p0501 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0491 p0500
  have p0502 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0503 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0504 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv v) C) p0502 p0503
  have p0505 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0506 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0507 :=
    @g_simpl (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0508 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classMem (.cv u) C) p0506 p0507
  have p0509 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classMem (.cv u) C) p0505 p0508
  have p0510 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv u) C) p0504 p0509
  have p0511 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0501 p0510
  have p0512 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      p0480 p0511
  have p0513 := @g_brlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0514 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C))))
      (syn_wb (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
          (syn_cec (.cv u) (syn_clnker R))) (syn_wbr (.cv v) R (.cv u)))
      p0512 p0513
  have p0515 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))
      (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
        (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv v) R (.cv u)) p0471 p0514
  have p0516 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)) (syn_wbr (.cv v) R (.cv u)) p0460 p0515
  have p0517 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wbr (.cv v) R (.cv u)) p0453 p0516
  have p0518 :=
    @g_trd
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      C R (.cv t) (.cv v) (.cv u) p0410 p0434 p0439 p0446 p0452 p0517
  have p0519 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u)) p0395 p0518
  have p0520 := @g_ellnkerecg (.cv t) (.cv u) R
  have p0521 :=
    @g_a1i
      (syn_wb (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
        (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))))
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      p0520
  have p0522 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_w3a
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
              (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
                (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
              (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
          (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
        (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv t)) (syn_wbr (.cv t) R (.cv u))) p0519 p0521
  have p0523 :=
    @g_ex
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R)))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R))) p0522
  have p0524 :=
    @g_impbid
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (.classMem (.cv t) (syn_cec (.cv u) (syn_clnker R)))
      (.classMem (.cv t) (syn_cec (.cv v) (syn_clnker R))) p0272 p0523
  have p0525 :=
    @g_eqrdv
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      t (syn_cec (.cv u) (syn_clnker R)) (syn_cec (.cv v) (syn_clnker R)) dv_cache_0012
      dv_cache_0013 dv_cache_0014 p0524
  have p0526 :=
    @g_simpl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0527 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
  have p0528 :=
    @g_simpr (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))
  have p0529 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv u) C) (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0527 p0528
  have p0530 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) p0526 p0529
  have p0531 :=
    @g_simpr
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  have p0532 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0533 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0531 p0532
  have p0534 :=
    @g_n_3eqtr4d
      (syn_wa (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
            (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
              (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
            (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))))) (syn_wa (.classMem (.cv v) C)
          (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      (syn_cec (.cv u) (syn_clnker R)) (syn_cec (.cv v) (syn_clnker R)) (.cv x) (.cv y)
      p0525 p0530 p0533
  have p0535 :=
    @g_rexlimddv
      (syn_wa (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (syn_wa (.classMem (.cv u) C)
          (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R)))))
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) (.classEq (.cv x) (.cv y)) v C
      dv_cache_0015 dv_cache_0016 p0021 p0534
  have p0536 :=
    @g_rexlimddv
      (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
        (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
          (syn_wbr (.cv y) (syn_clnqord R C) (.cv x))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_clnker R))) (.classEq (.cv x) (.cv y)) u C
      dv_cache_0017 dv_cache_0018 p0012 p0535
  have p0537_e02_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem (.cv x) (syn_clnquo R C)) (.classMem (.cv y) (syn_clnquo R C)))
          (syn_wa (syn_wbr (.cv x) (syn_clnqord R C) (.cv y))
            (syn_wbr (.cv y) (syn_clnqord R C) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0536
  have p0537 :=
    @g_antird
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      x y (syn_clnquo R C) (syn_clnqord R C) (syn_cvv) (syn_cvv) dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      p0002 p0005 p0537_e02_recanon
  exact p0537


end NFChoice.DirectNominalPrf.WPPReplay
