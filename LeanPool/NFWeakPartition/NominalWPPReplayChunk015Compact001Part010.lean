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

/-- Checked nominal proof certificate identified upstream as `g_lnqordantisym`. -/
@[expose]
noncomputable def gLnqordantisym (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWbr (synClnqord R C) (synCantisym) (synClnquo R C))) :=
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
  have dv_cache_0012 : t ∉ ((synCec (.cv u) (synClnker R))).fv :=
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
  have dv_cache_0013 : t ∉ ((synCec (.cv v) (synClnker R))).fv :=
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
      ((synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
                (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C)
            (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))).fv :=
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
      ((synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))).fv :=
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
      ((synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x))))).fv :=
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
  have dv_cache_0019 : x ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0020 : y ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0021 : x ∉ ((synClnqord R C)).fv :=
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
  have dv_cache_0022 : y ∉ ((synClnqord R C)).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
      ((synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))).fv :=
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
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0001 := @gLnqordexg C R dv_cache_0001
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnqord R C) (synCvv)) p0000 p0001
  have p0004 := @gLnquoexg C R dv_cache_0001
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnquo R C) (synCvv)) p0000 p0004
  have p0006 :=
    @gSimp2
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0007 :=
    @gSimpl (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
  have p0008 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (.classMem (.cv x) (synClnquo R C)) p0006 p0007
  have p0009 := @gVex x
  have p0010 :=
    @gEllnquo u C (.cv x) R dv_cache_0002 dv_cache_0001 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0009
  have p0011 :=
    @gBiimpi (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0010
  have p0012 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (.classMem (.cv x) (synClnquo R C))
      (synWrex u C (.classEq (.cv x) (synCec (.cv u) (synClnker R)))) p0008 p0011
  have p0013 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0014 :=
    @gSimp2
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0015 :=
    @gSimpr (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C))
  have p0016 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (.classMem (.cv y) (synClnquo R C)) p0014 p0015
  have p0017 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (.classMem (.cv y) (synClnquo R C)) p0013 p0016
  have p0018 := @gVex y
  have p0019 :=
    @gEllnquo v C (.cv y) R dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0018
  have p0020 :=
    @gBiimpi (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0019
  have p0021 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0017 p0020
  have p0022 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0023 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0024 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0025 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0026 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0024 p0025
  have p0027 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0023 p0026
  have p0028 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0029 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0030 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0028 p0029
  have p0031 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0032 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0030 p0031
  have p0033 := @gSimpr (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCtrans) C) p0032 p0033
  have p0035 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCtrans) C) p0027 p0034
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr R (synCtrans) C) p0022 p0035
  have p0037 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0038 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0039 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0040 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0038 p0039
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) p0037 p0040
  have p0042 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0043 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0044 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0045 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0046 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0044 p0045
  have p0047 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0043 p0046
  have p0048 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) p0042 p0047
  have p0049 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0050 := @gEllnkerecg (.cv t) (.cv u) R
  have p0051 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0050
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0049 p0051
  have p0053 := @gSimpl (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))
  have p0054 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u)))
      (synWbr (.cv u) R (.cv t)) p0052 p0053
  have p0055 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0056 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0057 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0058 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0059 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0057 p0058
  have p0060 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0056 p0059
  have p0061 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0062 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0063 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0061 p0062
  have p0064 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0060 p0063
  have p0065 :=
    @gSsbrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      R (synCxp C C) (.cv u) (.cv t) p0064
  have p0066 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.imp (synWbr (.cv u) R (.cv t)) (synWbr (.cv u) (synCxp C C) (.cv t))) p0055
      p0065
  have p0067 :=
    @gMpd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWbr (.cv u) R (.cv t)) (synWbr (.cv u) (synCxp C C) (.cv t)) p0054 p0066
  have p0068 := @gBrxp (.cv u) (.cv t) C C
  have p0069 :=
    @gA1i
      (synWb (synWbr (.cv u) (synCxp C C) (.cv t))
        (synWa (.classMem (.cv u) C) (.classMem (.cv t) C)))
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      p0068
  have p0070 :=
    @gMpbid
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWbr (.cv u) (synCxp C C) (.cv t))
      (synWa (.classMem (.cv u) C) (.classMem (.cv t) C)) p0067 p0069
  have p0071 := @gSimpr (.classMem (.cv u) C) (.classMem (.cv t) C)
  have p0072 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (.classMem (.cv u) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0070
      p0071
  have p0073 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0074 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0075 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0076 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      p0074 p0075
  have p0077 :=
    @gSimp3
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0078 :=
    @gSimpr (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
  have p0079 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) p0077 p0078
  have p0080 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) p0076 p0079
  have p0081 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0082 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0083 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0081 p0082
  have p0084 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0085 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0086 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0087 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0085 p0086
  have p0088 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0084 p0087
  have p0089 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0083 p0088
  have p0090 :=
    @gBreq12 (.cv y) (synCec (.cv v) (synClnker R)) (.cv x)
      (synCec (.cv u) (synClnker R)) (synClnqord R C)
  have p0091 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
        (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (synWb (synWbr (.cv y) (synClnqord R C) (.cv x))
        (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))))
      p0089 p0090
  have p0092 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0093 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0094 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0095 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0093 p0094
  have p0096 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0092 p0095
  have p0097 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0098 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0099 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0097 p0098
  have p0100 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0096 p0099
  have p0101 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0102 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0103 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0104 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0102 p0103
  have p0105 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0101 p0104
  have p0106 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0107 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0108 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0106 p0107
  have p0109 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0110 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0108 p0109
  have p0111 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0105 p0110
  have p0112 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0113 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0114 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0115 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0113 p0114
  have p0116 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0112 p0115
  have p0117 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0118 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0119 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0117 p0118
  have p0120 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0116 p0119
  have p0121 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0111 p0120
  have p0122 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0123 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0124 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0122 p0123
  have p0125 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0126 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0127 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0128 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0126 p0127
  have p0129 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0125 p0128
  have p0130 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv u) C) p0124 p0129
  have p0131 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0121 p0130
  have p0132 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      p0100 p0131
  have p0133 := @gBrlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0134 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv u) C))))
      (synWb (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))) (synWbr (.cv v) R (.cv u)))
      p0132 p0133
  have p0135 :=
    @gBitrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
      (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
        (synCec (.cv u) (synClnker R)))
      (synWbr (.cv v) R (.cv u)) p0091 p0134
  have p0136 :=
    @gMpbid
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) (synWbr (.cv v) R (.cv u)) p0080 p0135
  have p0137 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv v) R (.cv u)) p0073 p0136
  have p0138 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0139 := @gEllnkerecg (.cv t) (.cv u) R
  have p0140 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0139
  have p0141 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0138 p0140
  have p0142 := @gSimpl (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))
  have p0143 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u)))
      (synWbr (.cv u) R (.cv t)) p0141 p0142
  have p0144 :=
    @gTrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      C R (.cv v) (.cv u) (.cv t) p0036 p0041 p0048 p0072 p0137 p0143
  have p0145 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0146 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0147 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0148 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0149 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0147 p0148
  have p0150 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0146 p0149
  have p0151 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0152 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0153 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0151 p0152
  have p0154 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0155 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0153 p0154
  have p0156 := @gSimpr (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0157 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCtrans) C) p0155 p0156
  have p0158 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCtrans) C) p0150 p0157
  have p0159 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr R (synCtrans) C) p0145 p0158
  have p0160 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0161 := @gEllnkerecg (.cv t) (.cv u) R
  have p0162 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0161
  have p0163 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0160 p0162
  have p0164 := @gSimpl (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))
  have p0165 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u)))
      (synWbr (.cv u) R (.cv t)) p0163 p0164
  have p0166 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0167 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0168 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0169 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0170 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0168 p0169
  have p0171 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0167 p0170
  have p0172 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0173 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0174 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0172 p0173
  have p0175 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0171 p0174
  have p0176 :=
    @gSsbrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      R (synCxp C C) (.cv u) (.cv t) p0175
  have p0177 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.imp (synWbr (.cv u) R (.cv t)) (synWbr (.cv u) (synCxp C C) (.cv t))) p0166
      p0176
  have p0178 :=
    @gMpd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWbr (.cv u) R (.cv t)) (synWbr (.cv u) (synCxp C C) (.cv t)) p0165 p0177
  have p0179 := @gBrxp (.cv u) (.cv t) C C
  have p0180 :=
    @gA1i
      (synWb (synWbr (.cv u) (synCxp C C) (.cv t))
        (synWa (.classMem (.cv u) C) (.classMem (.cv t) C)))
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      p0179
  have p0181 :=
    @gMpbid
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWbr (.cv u) (synCxp C C) (.cv t))
      (synWa (.classMem (.cv u) C) (.classMem (.cv t) C)) p0178 p0180
  have p0182 := @gSimpr (.classMem (.cv u) C) (.classMem (.cv t) C)
  have p0183 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (.classMem (.cv u) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0181
      p0182
  have p0184 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0185 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0186 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0187 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0188 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0186 p0187
  have p0189 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0185 p0188
  have p0190 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) p0184 p0189
  have p0191 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0192 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0193 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0194 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0192 p0193
  have p0195 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) p0191 p0194
  have p0196 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0197 := @gEllnkerecg (.cv t) (.cv u) R
  have p0198 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0197
  have p0199 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0196 p0198
  have p0200 := @gSimpr (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))
  have p0201 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u)))
      (synWbr (.cv t) R (.cv u)) p0199 p0200
  have p0202 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
  have p0203 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0204 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0205 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      p0203 p0204
  have p0206 :=
    @gSimp3
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0207 :=
    @gSimpl (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
  have p0208 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) p0206 p0207
  have p0209 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) p0205 p0208
  have p0210 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0211 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0212 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0213 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0211 p0212
  have p0214 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0210 p0213
  have p0215 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0216 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0217 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0215 p0216
  have p0218 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0214 p0217
  have p0219 :=
    @gBreq12 (.cv x) (synCec (.cv u) (synClnker R)) (.cv y)
      (synCec (.cv v) (synClnker R)) (synClnqord R C)
  have p0220 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
        (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (synWb (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))))
      p0218 p0219
  have p0221 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0222 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0223 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0224 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0222 p0223
  have p0225 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0221 p0224
  have p0226 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0227 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0228 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0226 p0227
  have p0229 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0225 p0228
  have p0230 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0231 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0232 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0233 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0231 p0232
  have p0234 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0230 p0233
  have p0235 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0236 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0237 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0235 p0236
  have p0238 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0239 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0237 p0238
  have p0240 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0234 p0239
  have p0241 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0242 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0243 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0244 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0242 p0243
  have p0245 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0241 p0244
  have p0246 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0247 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0248 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0246 p0247
  have p0249 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0245 p0248
  have p0250 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0240 p0249
  have p0251 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0252 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0253 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0254 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0252 p0253
  have p0255 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0251 p0254
  have p0256 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0257 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0258 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0256 p0257
  have p0259 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0255 p0258
  have p0260 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0250 p0259
  have p0261 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0229 p0260
  have p0262 := @gBrlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0263 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (synWb (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))) (synWbr (.cv u) R (.cv v)))
      p0261 p0262
  have p0264 :=
    @gBitrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
        (synCec (.cv v) (synClnker R)))
      (synWbr (.cv u) R (.cv v)) p0220 p0263
  have p0265 :=
    @gMpbid
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) (synWbr (.cv u) R (.cv v)) p0209 p0264
  have p0266 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv u) R (.cv v)) p0202 p0265
  have p0267 :=
    @gTrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      C R (.cv t) (.cv u) (.cv v) p0159 p0183 p0190 p0195 p0201 p0266
  have p0268 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v)) p0144 p0267
  have p0269 := @gEllnkerecg (.cv t) (.cv v) R
  have p0270 :=
    @gA1i
      (synWb (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
        (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))))
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      p0269
  have p0271 :=
    @gMpbird
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0268 p0270
  have p0272 :=
    @gEx
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R))) p0271
  have p0273 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0274 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0275 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0276 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0277 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0275 p0276
  have p0278 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0274 p0277
  have p0279 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0280 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0281 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0279 p0280
  have p0282 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0283 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0281 p0282
  have p0284 := @gSimpr (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0285 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCtrans) C) p0283 p0284
  have p0286 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCtrans) C) p0278 p0285
  have p0287 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr R (synCtrans) C) p0273 p0286
  have p0288 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0289 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0290 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0291 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0292 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0290 p0291
  have p0293 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0289 p0292
  have p0294 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) p0288 p0293
  have p0295 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0296 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0297 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0298 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0296 p0297
  have p0299 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) p0295 p0298
  have p0300 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0301 := @gEllnkerecg (.cv t) (.cv v) R
  have p0302 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0301
  have p0303 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0300 p0302
  have p0304 := @gSimpl (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))
  have p0305 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v)))
      (synWbr (.cv v) R (.cv t)) p0303 p0304
  have p0306 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0307 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0308 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0309 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0310 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0308 p0309
  have p0311 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0307 p0310
  have p0312 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0313 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0314 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0312 p0313
  have p0315 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0311 p0314
  have p0316 :=
    @gSsbrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      R (synCxp C C) (.cv v) (.cv t) p0315
  have p0317 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.imp (synWbr (.cv v) R (.cv t)) (synWbr (.cv v) (synCxp C C) (.cv t))) p0306
      p0316
  have p0318 :=
    @gMpd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWbr (.cv v) R (.cv t)) (synWbr (.cv v) (synCxp C C) (.cv t)) p0305 p0317
  have p0319 := @gBrxp (.cv v) (.cv t) C C
  have p0320 :=
    @gA1i
      (synWb (synWbr (.cv v) (synCxp C C) (.cv t))
        (synWa (.classMem (.cv v) C) (.classMem (.cv t) C)))
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      p0319
  have p0321 :=
    @gMpbid
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWbr (.cv v) (synCxp C C) (.cv t))
      (synWa (.classMem (.cv v) C) (.classMem (.cv t) C)) p0318 p0320
  have p0322 := @gSimpr (.classMem (.cv v) C) (.classMem (.cv t) C)
  have p0323 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (.classMem (.cv v) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0321
      p0322
  have p0324 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0325 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0326 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0327 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      p0325 p0326
  have p0328 :=
    @gSimp3
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0329 :=
    @gSimpl (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
  have p0330 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) p0328 p0329
  have p0331 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) p0327 p0330
  have p0332 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0333 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0334 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0335 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0333 p0334
  have p0336 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0332 p0335
  have p0337 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0338 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0339 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0337 p0338
  have p0340 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0336 p0339
  have p0341 :=
    @gBreq12 (.cv x) (synCec (.cv u) (synClnker R)) (.cv y)
      (synCec (.cv v) (synClnker R)) (synClnqord R C)
  have p0342 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
        (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (synWb (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))))
      p0340 p0341
  have p0343 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0344 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0345 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0346 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0344 p0345
  have p0347 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0343 p0346
  have p0348 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0349 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0350 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0348 p0349
  have p0351 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0347 p0350
  have p0352 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0353 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0354 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0355 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0353 p0354
  have p0356 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0352 p0355
  have p0357 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0358 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0359 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0357 p0358
  have p0360 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0361 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0359 p0360
  have p0362 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0356 p0361
  have p0363 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0364 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0365 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0366 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0364 p0365
  have p0367 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0363 p0366
  have p0368 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0369 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0370 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0368 p0369
  have p0371 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0367 p0370
  have p0372 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0362 p0371
  have p0373 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0374 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0375 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0376 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0374 p0375
  have p0377 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0373 p0376
  have p0378 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0379 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0380 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0378 p0379
  have p0381 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) (.classMem (.cv v) C) p0377 p0380
  have p0382 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)) p0372 p0381
  have p0383 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C)))
      p0351 p0382
  have p0384 := @gBrlnqordkern C R (.cv u) (.cv v) dv_cache_0001
  have p0385 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv u) C) (.classMem (.cv v) C))))
      (synWb (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
          (synCec (.cv v) (synClnker R))) (synWbr (.cv u) R (.cv v)))
      p0383 p0384
  have p0386 :=
    @gBitrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (synCec (.cv u) (synClnker R)) (synClnqord R C)
        (synCec (.cv v) (synClnker R)))
      (synWbr (.cv u) R (.cv v)) p0342 p0385
  have p0387 :=
    @gMpbid
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv x) (synClnqord R C) (.cv y)) (synWbr (.cv u) R (.cv v)) p0331 p0386
  have p0388 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv u) R (.cv v)) p0324 p0387
  have p0389 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0390 := @gEllnkerecg (.cv t) (.cv v) R
  have p0391 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0390
  have p0392 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0389 p0391
  have p0393 := @gSimpl (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))
  have p0394 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v)))
      (synWbr (.cv v) R (.cv t)) p0392 p0393
  have p0395 :=
    @gTrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      C R (.cv u) (.cv v) (.cv t) p0287 p0294 p0299 p0323 p0388 p0394
  have p0396 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0397 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0398 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0399 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0400 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0398 p0399
  have p0401 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0397 p0400
  have p0402 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0403 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0404 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0402 p0403
  have p0405 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0406 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0404 p0405
  have p0407 := @gSimpr (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0408 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCtrans) C) p0406 p0407
  have p0409 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr R (synCtrans) C) p0401 p0408
  have p0410 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr R (synCtrans) C) p0396 p0409
  have p0411 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0412 := @gEllnkerecg (.cv t) (.cv v) R
  have p0413 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0412
  have p0414 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0411 p0413
  have p0415 := @gSimpl (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))
  have p0416 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v)))
      (synWbr (.cv v) R (.cv t)) p0414 p0415
  have p0417 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0418 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0419 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0420 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0421 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0419 p0420
  have p0422 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0418 p0421
  have p0423 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0424 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0425 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0423 p0424
  have p0426 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0422 p0425
  have p0427 :=
    @gSsbrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      R (synCxp C C) (.cv v) (.cv t) p0426
  have p0428 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.imp (synWbr (.cv v) R (.cv t)) (synWbr (.cv v) (synCxp C C) (.cv t))) p0417
      p0427
  have p0429 :=
    @gMpd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWbr (.cv v) R (.cv t)) (synWbr (.cv v) (synCxp C C) (.cv t)) p0416 p0428
  have p0430 := @gBrxp (.cv v) (.cv t) C C
  have p0431 :=
    @gA1i
      (synWb (synWbr (.cv v) (synCxp C C) (.cv t))
        (synWa (.classMem (.cv v) C) (.classMem (.cv t) C)))
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      p0430
  have p0432 :=
    @gMpbid
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWbr (.cv v) (synCxp C C) (.cv t))
      (synWa (.classMem (.cv v) C) (.classMem (.cv t) C)) p0429 p0431
  have p0433 := @gSimpr (.classMem (.cv v) C) (.classMem (.cv t) C)
  have p0434 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (.classMem (.cv v) C) (.classMem (.cv t) C)) (.classMem (.cv t) C) p0432
      p0433
  have p0435 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0436 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0437 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0438 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0436 p0437
  have p0439 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) p0435 p0438
  have p0440 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0441 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0442 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0443 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0444 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0442 p0443
  have p0445 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0441 p0444
  have p0446 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv u) C) p0440 p0445
  have p0447 :=
    @gSimpr
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0448 := @gEllnkerecg (.cv t) (.cv v) R
  have p0449 :=
    @gBiimpi (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0448
  have p0450 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))) p0447 p0449
  have p0451 := @gSimpr (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v))
  have p0452 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWbr (.cv v) R (.cv t)) (synWbr (.cv t) R (.cv v)))
      (synWbr (.cv t) R (.cv v)) p0450 p0451
  have p0453 :=
    @gSimpl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
  have p0454 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0455 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0456 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      p0454 p0455
  have p0457 :=
    @gSimp3
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0458 :=
    @gSimpr (synWbr (.cv x) (synClnqord R C) (.cv y))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
  have p0459 :=
    @gSyl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) p0457 p0458
  have p0460 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) p0456 p0459
  have p0461 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0462 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0463 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0461 p0462
  have p0464 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0465 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0466 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0467 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0465 p0466
  have p0468 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0464 p0467
  have p0469 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0463 p0468
  have p0470 :=
    @gBreq12 (.cv y) (synCec (.cv v) (synClnker R)) (.cv x)
      (synCec (.cv u) (synClnker R)) (synClnqord R C)
  have p0471 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
        (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (synWb (synWbr (.cv y) (synClnqord R C) (.cv x))
        (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))))
      p0469 p0470
  have p0472 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0473 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0474 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0475 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0473 p0474
  have p0476 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0472 p0475
  have p0477 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0478 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0479 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0477 p0478
  have p0480 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (.classMem R (synCvv)) p0476 p0479
  have p0481 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0482 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0483 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0484 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0482 p0483
  have p0485 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0481 p0484
  have p0486 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0487 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0488 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0486 p0487
  have p0489 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0490 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0488 p0489
  have p0491 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0485 p0490
  have p0492 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0493 :=
    @gSimpl
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0494 :=
    @gSimp1
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
      (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
        (synWbr (.cv y) (synClnqord R C) (.cv x)))
  have p0495 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0493 p0494
  have p0496 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0492 p0495
  have p0497 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0498 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0499 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0497 p0498
  have p0500 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0496 p0499
  have p0501 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0491 p0500
  have p0502 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0503 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0504 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv v) C) p0502 p0503
  have p0505 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0506 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0507 :=
    @gSimpl (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0508 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classMem (.cv u) C) p0506 p0507
  have p0509 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classMem (.cv u) C) p0505 p0508
  have p0510 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv v) C) (.classMem (.cv u) C) p0504 p0509
  have p0511 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0501 p0510
  have p0512 :=
    @gJca
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      p0480 p0511
  have p0513 := @gBrlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0514 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem (.cv v) C) (.classMem (.cv u) C))))
      (synWb (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
          (synCec (.cv u) (synClnker R))) (synWbr (.cv v) R (.cv u)))
      p0512 p0513
  have p0515 :=
    @gBitrd
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv x))
      (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
        (synCec (.cv u) (synClnker R)))
      (synWbr (.cv v) R (.cv u)) p0471 p0514
  have p0516 :=
    @gMpbid
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv y) (synClnqord R C) (.cv x)) (synWbr (.cv v) R (.cv u)) p0460 p0515
  have p0517 :=
    @gSyl
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWbr (.cv v) R (.cv u)) p0453 p0516
  have p0518 :=
    @gTrd
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      C R (.cv t) (.cv v) (.cv u) p0410 p0434 p0439 p0446 p0452 p0517
  have p0519 :=
    @gJca
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u)) p0395 p0518
  have p0520 := @gEllnkerecg (.cv t) (.cv u) R
  have p0521 :=
    @gA1i
      (synWb (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
        (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))))
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      p0520
  have p0522 :=
    @gMpbird
      (synWa (synWa (synWa (synW3a
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
              (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
                (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
              (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
          (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
        (.classMem (.cv t) (synCec (.cv v) (synClnker R))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv t)) (synWbr (.cv t) R (.cv u))) p0519 p0521
  have p0523 :=
    @gEx
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R)))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R))) p0522
  have p0524 :=
    @gImpbid
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (.classMem (.cv t) (synCec (.cv u) (synClnker R)))
      (.classMem (.cv t) (synCec (.cv v) (synClnker R))) p0272 p0523
  have p0525 :=
    @gEqrdv
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      t (synCec (.cv u) (synClnker R)) (synCec (.cv v) (synClnker R)) dv_cache_0012
      dv_cache_0013 dv_cache_0014 p0524
  have p0526 :=
    @gSimpl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0527 :=
    @gSimpr
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
  have p0528 :=
    @gSimpr (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R)))
  have p0529 :=
    @gSyl
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv u) C) (.classEq (.cv x) (synCec (.cv u) (synClnker R))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0527 p0528
  have p0530 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) p0526 p0529
  have p0531 :=
    @gSimpr
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  have p0532 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0533 :=
    @gSyl
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0531 p0532
  have p0534 :=
    @gN3eqtr4d
      (synWa (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
            (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
              (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
            (.classEq (.cv x) (synCec (.cv u) (synClnker R))))) (synWa (.classMem (.cv v) C)
          (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      (synCec (.cv u) (synClnker R)) (synCec (.cv v) (synClnker R)) (.cv x) (.cv y)
      p0525 p0530 p0533
  have p0535 :=
    @gRexlimddv
      (synWa (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (synWa (.classMem (.cv u) C)
          (.classEq (.cv x) (synCec (.cv u) (synClnker R)))))
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) (.classEq (.cv x) (.cv y)) v C
      dv_cache_0015 dv_cache_0016 p0021 p0534
  have p0536 :=
    @gRexlimddv
      (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
        (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
          (synWbr (.cv y) (synClnqord R C) (.cv x))))
      (.classEq (.cv x) (synCec (.cv u) (synClnker R))) (.classEq (.cv x) (.cv y)) u C
      dv_cache_0017 dv_cache_0018 p0012 p0535
  have p0537_e02_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem (.cv x) (synClnquo R C)) (.classMem (.cv y) (synClnquo R C)))
          (synWa (synWbr (.cv x) (synClnqord R C) (.cv y))
            (synWbr (.cv y) (synClnqord R C) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0536
  have p0537 :=
    @gAntird
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      x y (synClnquo R C) (synClnqord R C) (synCvv) (synCvv) dv_cache_0019
      dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
      p0002 p0005 p0537_e02_recanon
  exact p0537


end NFChoice.DirectNominalPrf.WPPReplay
