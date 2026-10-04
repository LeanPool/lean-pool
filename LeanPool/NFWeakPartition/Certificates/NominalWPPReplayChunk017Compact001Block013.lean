/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part059`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wpphitprefixtransferpackdndv`. -/
@[expose]
noncomputable def gWpphitprefixtransferpackdndv (k : Var) (F : Class) (G : Class)
    (I : Class) (L : Class) (q : Var) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv)
    (dv_I_q : q ∉ I.fv) (dv_L_q : q ∉ L.fv) (dv_k_q : k ≠ q)
    (hyp_wpphitprefixtransferpackdndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wpphitprefixtransferpackdndv_2 : Nominal.NPrf (.classMem I (synCdm F)))
    (hyp_wpphitprefixtransferpackdndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wpphitprefixtransferpackdndv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wpphitprefixtransferpackdndv_5 : Nominal.NPrf (.classMem I (synCdm G)))
    (hyp_wpphitprefixtransferpackdndv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wpphitprefixtransferpackdndv_7 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv q))))
            (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L))))
    (hyp_wpphitprefixtransferpackdndv_8 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L)
            (.classEq (synCfv F (synCfv (synCfrec G I) (.cv q)))
              (synCfv G (synCfv (synCfrec G I) (.cv q))))))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.classMem (.cv k) (synCwpphit G I L)) (synWral q (synCnnc)
              (.imp (.classMem (.cv q) (synCwpphit G I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
        (synWa (.classMem (.cv k) (synCwpphit F I L))
          (.classEq (synCfv (synCfrec G I) (.cv k)) (synCfv (synCfrec F I) (.cv k))))) :=
  by
  let proofSupport : Finset Var :=
    ({ k } : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv ∪ L.fv ∪ ({ q } : Finset Var)
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  let r : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_ne_k : n ≠ k := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_L : n ∉ L.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_q : n ≠ q := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_k : x ≠ k := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_k : y ≠ k := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_L : y ∉ L.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_q : y ≠ q := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_ne_k : a ≠ k := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_ne_k : z ≠ k := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_z_ne_r : z ≠ r :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_r_ne_z : r ≠ z := Ne.symm fresh_z_ne_r
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_r_ne_b : r ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_r : b ≠ r := Ne.symm fresh_r_ne_b
  have dv_cache_0001 : x ∉ ((synCwppfrecprefixeq F G I k)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G,
          fresh_x_not_I, fresh_x_ne_k, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (synC0c) (synCwppfrecprefixeq F G I k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G,
          fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (synCwppfrecprefixeq F G I k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_F,
          fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
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
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : a ∉ ((Wff.classEq (.cv r) (synCkqrel (synClefin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv b)).fv :=
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
          fresh_z_ne_b, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv b)).fv :=
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
          fresh_a_ne_b, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_b, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 : b ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show b ≠ r from (by exact fresh_b_ne_r))
  have dv_cache_0016 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0017 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0018 : b ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show b ≠ z from (by exact fresh_b_ne_z))
  have dv_cache_0019 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0020 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0021 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0022 : x ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0023 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0024 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0025 : r ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0026 : b ∉ ((synCkqrel (synClefin))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0027 : r ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0028 : b ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0029 :
    r ∉
      ((synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_a,
          fresh_r_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0030 :
    b ∉
      ((synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a,
          fresh_b_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 : r ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show r ≠ b from (by exact fresh_r_ne_b))
  have dv_cache_0032 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0033 : z ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0034 : a ∉ ((synCplc (.cv y) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0035 : z ∉ ((synCplc (.cv y) (synC1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0036 : z ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_k, not_false_eq_true])
  have dv_cache_0037 :
    x ∉
      ((Wff.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_a, fresh_x_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0038 :
    z ∉
      ((Wff.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0039 :
    a ∉
      ((Wff.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0040 : x ∉ ((synCplc (.cv y) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0041 : a ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_k, not_false_eq_true])
  have dv_cache_0042 :
    x ∉
      ((Wff.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_a, fresh_x_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0043 :
    z ∉
      ((Wff.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0044 :
    a ∉
      ((Wff.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_k, fresh_a_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0045 : q ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_y, not_false_eq_true])
  have dv_cache_0046 : q ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0047 :
    q ∉
      ((Wff.imp (.classMem (.cv y) (synCwpphit G I L))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, dv_L_q, dv_G_q, dv_I_q, (Ne.symm dv_k_q),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0048 :
    q ∉
      ((Wff.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
          (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_L_q, fresh_q_ne_y, dv_G_q, dv_I_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0049 :
    q ∉
      ((Wff.imp (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L)
          (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
            (synCfv G (synCfv (synCfrec G I) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_y, dv_G_q, dv_I_q, dv_L_q, dv_F_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0050 :
    x ∉ ((Wff.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_F,
          fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0051 :
    y ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
            (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_k, fresh_y_not_L,
          fresh_y_not_G, fresh_y_not_I, fresh_y_ne_q, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0052 : y ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0053 :
    y ∉ ((Class.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_x,
          fresh_y_not_F, fresh_y_not_G, fresh_y_not_I, fresh_y_ne_k, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0054 : x ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_n, not_false_eq_true])
  have dv_cache_0055 : x ∉ ((Wff.classMem (.cv n) (synCwppfrecprefixeq F G I k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq,
          Finset.mem_union, Finset.mem_singleton, fresh_x_ne_n, fresh_x_not_F,
          fresh_x_not_G, fresh_x_not_I, fresh_x_ne_k, or_false, not_false_eq_true])
  have dv_cache_0056 :
    n ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
            (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
                (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_L,
          fresh_n_not_G, fresh_n_not_I, fresh_n_ne_q, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0057 : n ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_k, not_false_eq_true])
  have dv_cache_0058 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0059 :
    n ∉
      ((Wff.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
          (.classEq (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_F, fresh_n_not_I, fresh_n_not_G,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (.cv k) (synCwpphit G I L)) (synWral q (synCnnc)
          (.imp (.classMem (.cv q) (synCwpphit G I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
  have p0001 :=
    @gSimpr (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (.cv k) (synCwpphit G I L)) (synWral q (synCnnc)
          (.imp (.classMem (.cv q) (synCwpphit G I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
  have p0002 :=
    @gSimpl (.classMem (.cv k) (synCwpphit G I L))
      (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCwpphit G I L)) (synWral q (synCnnc)
          (.imp (.classMem (.cv q) (synCwpphit G I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      (.classMem (.cv k) (synCwpphit G I L)) p0001 p0002
  have p0004 :=
    @gN3pm32i (.classMem G (synCfuns)) (.classMem I (synCdm G))
      (synWss (synCrn G) (synCdm G)) hyp_wpphitprefixtransferpackdndv_4
      hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0005 := @gElwpphitvndv L G I (.cv k)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gSylib
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCwpphit G I L))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G I) (.cv k))))
      p0003 p0006
  have p0008 :=
    @gSimprd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv k))) p0007
  have p0009 := @gFinlewe
  have p0010 := @gWppweref (synCnnc) (synCkqrel (synClefin))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (.classMem (.cv k) (synCnnc)) p0011
  have p0013 := @gId (.classMem (.cv k) (synCnnc))
  have p0014 :=
    @gRefd (.classMem (.cv k) (synCnnc)) (synCnnc) (synCkqrel (synClefin)) (.cv k)
      p0012 p0013
  have p0015 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCnnc)) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
      p0000 p0014
  have p0016 := @gTru
  have p0017 :=
    @gWppfrecprefixeqexndv k F G I hyp_wpphitprefixtransferpackdndv_1
      hyp_wpphitprefixtransferpackdndv_4
  have p0018 := @gAbid2 x (synCwppfrecprefixeq F G I k) dv_cache_0001
  have p0019 :=
    @gEleq1i (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))
      (synCwppfrecprefixeq F G I k) (synCvv) p0018
  have p0020 :=
    @gMpbir
      (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
      (.classMem (synCwppfrecprefixeq F G I k) (synCvv)) p0017 p0019
  have p0021 :=
    @gA1i
      (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
      synWtru p0020
  have p0022 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wpphitprefixtransferpackdndv_1
      hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
  have p0023 := @gWpporbit0ndv F I
  have p0024 := Nominal.mp p0022 p0023
  have p0026 := @gWpporbit0ndv G I
  have p0027 := Nominal.mp p0004 p0026
  have p0028 := @gEqcomi (synCfv (synCfrec G I) (synC0c)) I p0027
  have p0029 :=
    @gEqtri (synCfv (synCfrec F I) (synC0c)) I (synCfv (synCfrec G I) (synC0c))
      p0024 p0028
  have p0030 :=
    @gA1i
      (.classEq (synCfv (synCfrec F I) (synC0c)) (synCfv (synCfrec G I) (synC0c)))
      (synWbr (synC0c) (synCkqrel (synClefin)) (.cv k)) p0029
  have p0031 := @gPeano1
  have p0032 :=
    @gWppfrecprefixeqvalndv (synC0c) k F G I hyp_wpphitprefixtransferpackdndv_1
      hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
      hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5
      hyp_wpphitprefixtransferpackdndv_6
  have p0033 := Nominal.mp p0031 p0032
  have p0034 :=
    @gMpbir (.classMem (synC0c) (synCwppfrecprefixeq F G I k))
      (.imp (synWbr (synC0c) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (synC0c)) (synCfv (synCfrec G I) (synC0c))))
      p0030 p0033
  have p0035 := @gA1i (.classMem (synC0c) (synCwppfrecprefixeq F G I k)) synWtru p0034
  have p0036 := @gN0cex
  have p0037 := @gId (.classEq (.cv x) (synC0c))
  have p0038 :=
    @gEleq1d (.classEq (.cv x) (synC0c)) (.cv x) (synC0c)
      (synCwppfrecprefixeq F G I k) p0037
  have p0039 :=
    @gElab (.classMem (.cv x) (synCwppfrecprefixeq F G I k))
      (.classMem (synC0c) (synCwppfrecprefixeq F G I k)) x (synC0c) dv_cache_0002
      dv_cache_0003 p0036 p0038
  have p0040 :=
    @gSylibr synWtru (.classMem (synC0c) (synCwppfrecprefixeq F G I k))
      (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      p0035 p0039
  have p0041 :=
    @gJca synWtru
      (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
      (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      p0021 p0040
  have p0042 := @gVex y
  have p0043 := @gId (.classEq (.cv x) (.cv y))
  have p0044 :=
    @gEleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) (synCwppfrecprefixeq F G I k)
      p0043
  have p0045 :=
    @gElab (.classMem (.cv x) (synCwppfrecprefixeq F G I k))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k)) x (.cv y) dv_cache_0004
      dv_cache_0005 p0042 p0044
  have p0047 :=
    @gA1i
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      p0022
  have p0048 :=
    @gSimp1 (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0049 :=
    @gJca
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem (.cv y) (synCnnc)) p0047 p0048
  have p0050 := @gWpporbitsucndv F I (.cv y)
  have p0051 :=
    @gSyl
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem (.cv y) (synCnnc)))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec F I) (.cv y))))
      p0049 p0050
  have p0053 :=
    @gSimp2 (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0054 :=
    @gJca
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      p0048 p0053
  have p0056 :=
    @gSimp3 (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0057 :=
    @gJca
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0048 p0056
  have p0058 :=
    @gSimpr (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0059 :=
    @gSimpl (.classMem (.cv y) (synCnnc))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0063 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (.classMem (.cv y) (synCnnc)) p0011
  have p0064 := @gId (.classMem (.cv y) (synCnnc))
  have p0065 :=
    @gRefd (.classMem (.cv y) (synCnnc)) (synCnnc) (synCkqrel (synClefin)) (.cv y)
      p0063 p0064
  have p0066 :=
    @gOrc (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
      (.classEq (.cv y) (synCplc (.cv y) (synC1c)))
  have p0067 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
      (synWo (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
        (.classEq (.cv y) (synCplc (.cv y) (synC1c))))
      p0065 p0066
  have p0070 :=
    @gJca (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCnnc)) p0064 p0064
  have p0071 := @gKqfinsucsplit (.cv y) (.cv y)
  have p0072 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (synWa (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWb (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
        (synWo (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
          (.classEq (.cv y) (synCplc (.cv y) (synC1c)))))
      p0070 p0071
  have p0073 :=
    @gMpbird (.classMem (.cv y) (synCnnc))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWo (synWbr (.cv y) (synCkqrel (synClefin)) (.cv y))
        (.classEq (.cv y) (synCplc (.cv y) (synC1c))))
      p0067 p0072
  have p0074 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))) p0059 p0073
  have p0075 :=
    @gA1d
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0074
  have p0076 :=
    @gAncom (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
  have p0078 := @gWppwepo (synCnnc) (synCkqrel (synClefin))
  have p0079 := Nominal.mp p0009 p0078
  have p0080 := @gPorta (synCnnc) (synCkqrel (synClefin))
  have p0081 :=
    @gMpbi (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
      (synW3a (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc)))
      p0079 p0080
  have p0082 :=
    @gSimp2 (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc))
  have p0083 := Nominal.mp p0081 p0082
  have p0084 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      p0083
  have p0085 := @gBrex (synCkqrel (synClefin)) (synCnnc) (synCtrans)
  have p0086 := @gBreq (.cv x) (.cv a) (.cv r) (synCkqrel (synClefin))
  have p0087 := @gBreq (.cv a) (.cv z) (.cv r) (synCkqrel (synClefin))
  have p0088 :=
    @gAnbi12d (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWbr (.cv x) (.cv r) (.cv a))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (.cv r) (.cv z))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)) p0086 p0087
  have p0089 := @gBreq (.cv x) (.cv z) (.cv r) (synCkqrel (synClefin))
  have p0090 :=
    @gImbi12d (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWa (synWbr (.cv x) (.cv r) (.cv a)) (synWbr (.cv a) (.cv r) (.cv z)))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (.cv x) (.cv r) (.cv z))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)) p0088 p0089
  have p0091 :=
    @gRalbidv (.classEq (.cv r) (synCkqrel (synClefin)))
      (.imp (synWa (synWbr (.cv x) (.cv r) (.cv a)) (synWbr (.cv a) (.cv r) (.cv z)))
        (synWbr (.cv x) (.cv r) (.cv z)))
      (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
          (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))
      z (.cv b) dv_cache_0006 p0090
  have p0092 :=
    @gN2ralbidv (.classEq (.cv r) (synCkqrel (synClefin)))
      (synWral z (.cv b)
        (.imp (synWa (synWbr (.cv x) (.cv r) (.cv a)) (synWbr (.cv a) (.cv r) (.cv z)))
          (synWbr (.cv x) (.cv r) (.cv z))))
      (synWral z (.cv b) (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))
      x a (.cv b) (.cv b) dv_cache_0007 dv_cache_0008 p0091
  have p0093 :=
    @gRaleq
      (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
          (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))
      z (.cv b) (synCnnc) dv_cache_0009 dv_cache_0010
  have p0094 :=
    @gRaleqbi1dv
      (synWral z (.cv b) (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))
      (synWral z (synCnnc) (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
            (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
          (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))
      a (.cv b) (synCnnc) dv_cache_0011 dv_cache_0012 p0093
  have p0095 :=
    @gRaleqbi1dv
      (synWral a (.cv b) (synWral z (.cv b) (.imp
            (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
              (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
            (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))))
      (synWral a (synCnnc) (synWral z (synCnnc) (.imp
            (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
              (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
            (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))))
      x (.cv b) (synCnnc) dv_cache_0013 dv_cache_0014 p0094
  have p0096 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans x a z r b
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0097 :=
    @gBrabg
      (synWral x (.cv b) (synWral a (.cv b) (synWral z (.cv b) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv a)) (synWbr (.cv a) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      (synWral x (.cv b) (synWral a (.cv b) (synWral z (.cv b) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      r b (synCkqrel (synClefin)) (synCnnc) (synCvv) (synCvv) (synCtrans)
      dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
      dv_cache_0031 p0092 p0095 p0096
  have p0098 :=
    @gSyl (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWa (.classMem (synCkqrel (synClefin)) (synCvv)) (.classMem (synCnnc) (synCvv)))
      (synWb (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc)) (synWral x (synCnnc)
          (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))))))
      p0085 p0097
  have p0099 :=
    @gIbi (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      p0098
  have p0100 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      p0084 p0099
  have p0103 := @gPeano2 (.cv y)
  have p0104 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc)) (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      p0059 p0103
  have p0105 :=
    @gJca
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc)) (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      p0059 p0104
  have p0106 :=
    @gA1d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      p0000
  have p0107 :=
    @g_pm3_2
      (synWa (.classMem (.cv y) (synCnnc))
        (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)))
      (.classMem (.cv k) (synCnnc))
  have p0108 :=
    @gSyl9
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (.cv y) (synCnnc))
        (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))) (.classMem (.cv k) (synCnnc)))
      p0106 p0107
  have p0109 :=
    @gSyl5
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv y) (synCnnc))
        (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.imp (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))) (synWa
          (synWa (.classMem (.cv y) (synCnnc))
            (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)))
          (.classMem (.cv k) (synCnnc))))
      p0105 p0108
  have p0110 :=
    @gPm243d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))) (.classMem (.cv k) (synCnnc)))
      p0109
  have p0111 :=
    (Nominal.biimpRefl (synW3a (.classMem (.cv y) (synCnnc))
        (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) (.classMem (.cv k) (synCnnc))))
  have p0112 :=
    @gSyl6ibr
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))) (.classMem (.cv k) (synCnnc)))
      (synW3a (.classMem (.cv y) (synCnnc))
        (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      p0110 p0111
  have p0113 := @gBreq1 (.cv x) (.cv y) (.cv a) (synCkqrel (synClefin))
  have p0114 :=
    @gAnbi1d (.classEq (.cv x) (.cv y))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)) p0113
  have p0115 := @gBreq1 (.cv x) (.cv y) (.cv z) (synCkqrel (synClefin))
  have p0116 :=
    @gImbi12d (.classEq (.cv x) (.cv y))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) p0114 p0115
  have p0117 :=
    @gBreq2 (.cv a) (synCplc (.cv y) (synC1c)) (.cv y) (synCkqrel (synClefin))
  have p0118 :=
    @gBreq1 (.cv a) (synCplc (.cv y) (synC1c)) (.cv z) (synCkqrel (synClefin))
  have p0119 :=
    @gAnbi12d (.classEq (.cv a) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)) p0117 p0118
  have p0120 :=
    @gImbi1d (.classEq (.cv a) (synCplc (.cv y) (synC1c)))
      (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) p0119
  have p0121 :=
    @gBreq2 (.cv z) (.cv k) (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin))
  have p0122 :=
    @gAnbi2d (.classEq (.cv z) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))) p0121
  have p0123 := @gBreq2 (.cv z) (.cv k) (.cv y) (synCkqrel (synClefin))
  have p0124 :=
    @gImbi12d (.classEq (.cv z) (.cv k))
      (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
      (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0122 p0123
  have p0125 :=
    @gRspc3v
      (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
          (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))
      (.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      (.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (.cv a))
          (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
      (.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
      x a z (.cv y) (synCplc (.cv y) (synC1c)) (.cv k) (synCnnc) (synCnnc) (synCnnc)
      dv_cache_0004 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
      dv_cache_0014 dv_cache_0014 dv_cache_0012 dv_cache_0014 dv_cache_0012 dv_cache_0010
      dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0022 dv_cache_0023 dv_cache_0024
      p0116 p0120 p0124
  have p0126 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (.classMem (.cv y) (synCnnc))
        (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (.imp (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))))) (.imp
          (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
      p0112 p0125
  have p0127 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      (.imp (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      p0100 p0126
  have p0128 :=
    @gSyl7bi
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))))
      (synWa (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0076 p0127
  have p0129 :=
    @gExp4a
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0128
  have p0130 :=
    Nominal.ax2 (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
  have p0131 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
      (.imp (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))))
        (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
      p0129 p0130
  have p0132 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc (.cv y) (synC1c))))
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      p0075 p0131
  have p0133 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0058 p0132
  have p0134 :=
    @gSyl5
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)) p0057 p0133
  have p0135 :=
    @g_pm3_2
      (synWa (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
  have p0136 :=
    @gSyl9
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
      (synWa (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      p0134 p0135
  have p0137 :=
    @gSyl5
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.imp (synW3a (.classMem (.cv y) (synCnnc))
          (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))) (synWa
          (synWa (.classMem (.cv y) (synCnnc))
            (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
      p0054 p0136
  have p0138 :=
    @gPm243d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      p0137
  have p0139 :=
    (Nominal.biimpRefl (synW3a (.classMem (.cv y) (synCnnc))
        (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))))
  have p0140 :=
    @gSyl6ibr
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (.classMem (.cv y) (synCwppfrecprefixeq F G I k)))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      p0138 p0139
  have p0141 :=
    @gWppfrecprefixeqvalndv (.cv y) k F G I hyp_wpphitprefixtransferpackdndv_1
      hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
      hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5
      hyp_wpphitprefixtransferpackdndv_6
  have p0142 :=
    @gBiimpd (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv y)) (synCfv (synCfrec G I) (.cv y))))
      p0141
  have p0143 :=
    @gN3imp (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k))
      (.classEq (synCfv (synCfrec F I) (.cv y)) (synCfv (synCfrec G I) (.cv y))) p0142
  have p0144 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv (synCfrec F I) (.cv y)) (synCfv (synCfrec G I) (.cv y))) p0140
      p0143
  have p0145 :=
    @gFveq2 (synCfv (synCfrec F I) (.cv y)) (synCfv (synCfrec G I) (.cv y)) F
  have p0146 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv (synCfrec F I) (.cv y)) (synCfv (synCfrec G I) (.cv y)))
      (.classEq (synCfv F (synCfv (synCfrec F I) (.cv y)))
        (synCfv F (synCfv (synCfrec G I) (.cv y))))
      p0144 p0145
  have p0147 :=
    @gEqeq2 (synCfv F (synCfv (synCfrec F I) (.cv y)))
      (synCfv F (synCfv (synCfrec G I) (.cv y)))
      (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
  have p0148 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv F (synCfv (synCfrec F I) (.cv y)))
        (synCfv F (synCfv (synCfrec G I) (.cv y))))
      (synWb (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec F I) (.cv y))))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec G I) (.cv y)))))
      p0146 p0147
  have p0149 :=
    @gBi1
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec F I) (.cv y))))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec G I) (.cv y))))
  have p0150 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWb (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec F I) (.cv y))))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec G I) (.cv y)))))
      (.imp (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec F I) (.cv y))))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec G I) (.cv y)))))
      p0148 p0149
  have p0151 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec F I) (.cv y))))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec G I) (.cv y))))
      p0051 p0150
  have p0156 := @gKqfinsucnle (.cv y)
  have p0157 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc))
      (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      p0059 p0156
  have p0158 := @gNotnot2 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0159 :=
    @gSimpr
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0160 :=
    @gSimpl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0162 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0160 p0058
  have p0163 :=
    @gA1d
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) p0162
  have p0164 :=
    @gAncom (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
  have p0172 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      p0083
  have p0188 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      p0172 p0099
  have p0193 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc)) p0160 p0104
  have p0195 :=
    @gSyl5
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCnnc)) p0160 p0106
  have p0196 :=
    @g_pm3_2 (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (.classMem (.cv k) (synCnnc))
  have p0197 :=
    @gSyl9
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.classMem (.cv k) (synCnnc)) (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)))
      p0195 p0196
  have p0198 :=
    @gSyl5
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.imp (synWa (synWa (.classMem (.cv y) (synCnnc))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
        (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
          (.classMem (.cv k) (synCnnc))))
      p0193 p0197
  have p0199 :=
    @gPm243d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)))
      p0198
  have p0202 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc)) p0160 p0059
  have p0203 :=
    @g_pm3_2
      (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)))
      (.classMem (.cv y) (synCnnc))
  have p0204 :=
    @gSyl5
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.classMem (.cv y) (synCnnc))
      (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)))
      (synWa (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
          (.classMem (.cv k) (synCnnc))) (.classMem (.cv y) (synCnnc)))
      p0202 p0203
  have p0205 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)))
      (.imp (synWa (synWa (.classMem (.cv y) (synCnnc))
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))) (synWa
          (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
            (.classMem (.cv k) (synCnnc))) (.classMem (.cv y) (synCnnc))))
      p0199 p0204
  have p0206 :=
    @gPm243d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
          (.classMem (.cv k) (synCnnc))) (.classMem (.cv y) (synCnnc)))
      p0205
  have p0207 :=
    (Nominal.biimpRefl (synW3a (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)) (.classMem (.cv y) (synCnnc))))
  have p0208 :=
    @gSyl6ibr
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (synWa (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
          (.classMem (.cv k) (synCnnc))) (.classMem (.cv y) (synCnnc)))
      (synW3a (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      p0206 p0207
  have p0209 :=
    @gBreq1 (.cv x) (synCplc (.cv y) (synC1c)) (.cv a) (synCkqrel (synClefin))
  have p0210 :=
    @gAnbi1d (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)) p0209
  have p0211 :=
    @gBreq1 (.cv x) (synCplc (.cv y) (synC1c)) (.cv z) (synCkqrel (synClefin))
  have p0212 :=
    @gImbi12d (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)) p0210 p0211
  have p0213 :=
    @gBreq2 (.cv a) (.cv k) (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin))
  have p0214 := @gBreq1 (.cv a) (.cv k) (.cv z) (synCkqrel (synClefin))
  have p0215 :=
    @gAnbi12d (.classEq (.cv a) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)) p0213 p0214
  have p0216 :=
    @gImbi1d (.classEq (.cv a) (.cv k))
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
        (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)) p0215
  have p0217 := @gBreq2 (.cv z) (.cv y) (.cv k) (synCkqrel (synClefin))
  have p0218 :=
    @gAnbi2d (.classEq (.cv z) (.cv y))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)) p0217
  have p0219 :=
    @gBreq2 (.cv z) (.cv y) (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin))
  have p0220 :=
    @gImbi12d (.classEq (.cv z) (.cv y))
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0218 p0219
  have p0221 :=
    @gRspc3v
      (.imp (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
          (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))
      (.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      (.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv a))
          (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
      (.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv z)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv z)))
      x a z (synCplc (.cv y) (synC1c)) (.cv k) (.cv y) (synCnnc) (synCnnc) (synCnnc)
      dv_cache_0040 dv_cache_0034 dv_cache_0035 dv_cache_0041 dv_cache_0036 dv_cache_0033
      dv_cache_0014 dv_cache_0014 dv_cache_0012 dv_cache_0014 dv_cache_0012 dv_cache_0010
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0022 dv_cache_0023 dv_cache_0024
      p0212 p0216 p0220
  have p0222 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synW3a (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
        (.classMem (.cv k) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.imp (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
                (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                  (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
                (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z)))))) (.imp
          (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      p0208 p0221
  have p0223 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWral x (synCnnc) (synWral a (synCnnc) (synWral z (synCnnc) (.imp
              (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv a))
                (synWbr (.cv a) (synCkqrel (synClefin)) (.cv z)))
              (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))))))
      (.imp (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      p0188 p0222
  have p0224 :=
    @gSyl7bi
      (synWa (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0164 p0223
  have p0225 :=
    @gExp4a
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0224
  have p0226 :=
    Nominal.ax2 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))
  have p0227 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      (.imp (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      p0225 p0226
  have p0228 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      p0163 p0227
  have p0229 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (synWa (.classMem (.cv y) (synCnnc))
          (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0159 p0228
  have p0230 :=
    @gExp3a
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0229
  have p0231 :=
    @gSyl7 (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0158 p0230
  have p0232 :=
    @gNotnot1 (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))
  have p0233 :=
    @gSyl8
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))
      (.neg (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      p0231 p0232
  have p0234 :=
    Nominal.ax3 (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
  have p0235 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.imp (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))) (.neg (.neg
            (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))))
      (.imp (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
        (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      p0233 p0234
  have p0236 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.neg (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))) p0157 p0235
  have p0237 := @gNotnot2 (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
  have p0239 :=
    @g_pm3_2 (.classMem (.cv y) (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
  have p0241 := @gElwpphitvndv L G I (.cv y)
  have p0242 := Nominal.mp p0004 p0241
  have p0243 :=
    @gBiimpri (.classMem (.cv y) (synCwpphit G I L))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
      p0242
  have p0244 :=
    @gSyl6 (.classMem (.cv y) (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
      (.classMem (.cv y) (synCwpphit G I L)) p0239 p0243
  have p0246 :=
    @gSimpr (.classMem (.cv k) (synCwpphit G I L))
      (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
  have p0247 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCwpphit G I L)) (synWral q (synCnnc)
          (.imp (.classMem (.cv q) (synCwpphit G I L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
      p0001 p0246
  have p0248 := @gId (.classEq (.cv q) (.cv y))
  have p0249 :=
    @gEleq1d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (synCwpphit G I L) p0248
  have p0251 :=
    @gBreq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (.cv k) (synCkqrel (synClefin))
      p0248
  have p0252 :=
    @gImbi12d (.classEq (.cv q) (.cv y)) (.classMem (.cv q) (synCwpphit G I L))
      (.classMem (.cv y) (synCwpphit G I L))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) p0249 p0251
  have p0253 :=
    @gRspcv
      (.imp (.classMem (.cv q) (synCwpphit G I L))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))
      (.imp (.classMem (.cv y) (synCwpphit G I L))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      q (.cv y) (synCnnc) dv_cache_0045 dv_cache_0046 dv_cache_0047 p0252
  have p0254 :=
    @gSyl5com
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))
      (.classMem (.cv y) (synCnnc))
      (.imp (.classMem (.cv y) (synCwpphit G I L))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      p0247 p0253
  have p0255 :=
    @gA1dd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc))
      (.imp (.classMem (.cv y) (synCwpphit G I L))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))) p0254
  have p0256 :=
    Nominal.ax2 (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
      (.classMem (.cv y) (synCwpphit G I L))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0257 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc))
      (.imp (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
        (.imp (.classMem (.cv y) (synCwpphit G I L))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      (.imp (.imp (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
          (.classMem (.cv y) (synCwpphit G I L)))
        (.imp (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))))
      p0255 p0256
  have p0258 :=
    @gMpdi
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc))
      (.imp (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
        (.classMem (.cv y) (synCwpphit G I L)))
      (.imp (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      p0244 p0257
  have p0259 :=
    @gSyl5
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.imp (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      p0059 p0258
  have p0260 :=
    @gSyl7 (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)) p0237 p0259
  have p0261 := @gNotnot1 (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
  have p0262 :=
    @gSyl8
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y))
      (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))) p0260 p0261
  have p0263 :=
    Nominal.ax3 (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
      (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
  have p0264 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.imp (.neg (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))))
        (.neg (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))))
      (.imp (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
        (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))))
      p0262 p0263
  have p0265 :=
    @gMpdd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.neg (synWbr (.cv k) (synCkqrel (synClefin)) (.cv y)))
      (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y)))) p0236 p0264
  have p0268 := @gFveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (synCfrec G I) p0248
  have p0269 :=
    @gBreq2d (.classEq (.cv q) (.cv y)) (synCfv (synCfrec G I) (.cv q))
      (synCfv (synCfrec G I) (.cv y)) L (synClec) p0268
  have p0270 :=
    @gNotbid (.classEq (.cv q) (.cv y))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv q)))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))) p0269
  have p0273 :=
    @gBreq1d (.classEq (.cv q) (.cv y)) (synCfv (synCfrec G I) (.cv q))
      (synCfv (synCfrec G I) (.cv y)) L (synClec) p0268
  have p0274 :=
    @gImbi12d (.classEq (.cv q) (.cv y))
      (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv q))))
      (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
      (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L)
      (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L) p0270 p0273
  have p0275 :=
    @gRspcv
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv q))))
        (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
        (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L))
      q (.cv y) (synCnnc) dv_cache_0045 dv_cache_0046 dv_cache_0048 p0274
  have p0276 :=
    @gMpi (.classMem (.cv y) (synCnnc))
      (synWral q (synCnnc)
        (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv q))))
          (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L)))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
        (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L))
      hyp_wpphitprefixtransferpackdndv_7 p0275
  have p0277 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc))
      (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
        (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L))
      p0059 p0276
  have p0278 :=
    @gSylcom
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.neg (synWbr L (synClec) (synCfv (synCfrec G I) (.cv y))))
      (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L) p0265 p0277
  have p0285 :=
    @gFveq2d (.classEq (.cv q) (.cv y)) (synCfv (synCfrec G I) (.cv q))
      (synCfv (synCfrec G I) (.cv y)) F p0268
  have p0288 :=
    @gFveq2d (.classEq (.cv q) (.cv y)) (synCfv (synCfrec G I) (.cv q))
      (synCfv (synCfrec G I) (.cv y)) G p0268
  have p0289 :=
    @gEqeq12d (.classEq (.cv q) (.cv y)) (synCfv F (synCfv (synCfrec G I) (.cv q)))
      (synCfv F (synCfv (synCfrec G I) (.cv y)))
      (synCfv G (synCfv (synCfrec G I) (.cv q)))
      (synCfv G (synCfv (synCfrec G I) (.cv y))) p0285 p0288
  have p0290 :=
    @gImbi12d (.classEq (.cv q) (.cv y))
      (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L)
      (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L)
      (.classEq (synCfv F (synCfv (synCfrec G I) (.cv q)))
        (synCfv G (synCfv (synCfrec G I) (.cv q))))
      (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      p0273 p0289
  have p0291 :=
    @gRspcv
      (.imp (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G I) (.cv q)))
          (synCfv G (synCfv (synCfrec G I) (.cv q)))))
      (.imp (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
          (synCfv G (synCfv (synCfrec G I) (.cv y)))))
      q (.cv y) (synCnnc) dv_cache_0045 dv_cache_0046 dv_cache_0049 p0290
  have p0292 :=
    @gMpi (.classMem (.cv y) (synCnnc))
      (synWral q (synCnnc) (.imp (synWbr (synCfv (synCfrec G I) (.cv q)) (synClec) L)
          (.classEq (synCfv F (synCfv (synCfrec G I) (.cv q)))
            (synCfv G (synCfv (synCfrec G I) (.cv q))))))
      (.imp (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
          (synCfv G (synCfv (synCfrec G I) (.cv y)))))
      hyp_wpphitprefixtransferpackdndv_8 p0291
  have p0293 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classMem (.cv y) (synCnnc))
      (.imp (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L)
        (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
          (synCfv G (synCfv (synCfrec G I) (.cv y)))))
      p0059 p0292
  have p0294 :=
    @gSylcom
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (synCfv (synCfrec G I) (.cv y)) (synClec) L)
      (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      p0278 p0293
  have p0295 :=
    @gSyl5
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv y) (synCnnc))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      p0057 p0294
  have p0296 :=
    @gEqeq2 (synCfv F (synCfv (synCfrec G I) (.cv y)))
      (synCfv G (synCfv (synCfrec G I) (.cv y)))
      (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
  have p0297 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv F (synCfv (synCfrec G I) (.cv y)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      (synWb (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec G I) (.cv y))))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv G (synCfv (synCfrec G I) (.cv y)))))
      p0295 p0296
  have p0298 :=
    @gBi1
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec G I) (.cv y))))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
  have p0299 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWb (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec G I) (.cv y))))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv G (synCfv (synCfrec G I) (.cv y)))))
      (.imp (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv F (synCfv (synCfrec G I) (.cv y))))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv G (synCfv (synCfrec G I) (.cv y)))))
      p0297 p0298
  have p0300 :=
    @gMpdd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv F (synCfv (synCfrec G I) (.cv y))))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      p0151 p0299
  have p0302 :=
    @gA1i
      (synW3a (.classMem G (synCfuns)) (.classMem I (synCdm G))
        (synWss (synCrn G) (synCdm G)))
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      p0004
  have p0304 :=
    @gJca
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (.classMem G (synCfuns)) (.classMem I (synCdm G))
        (synWss (synCrn G) (synCdm G)))
      (.classMem (.cv y) (synCnnc)) p0302 p0048
  have p0305 := @gWpporbitsucndv G I (.cv y)
  have p0306 :=
    @gSyl
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synW3a (.classMem G (synCfuns)) (.classMem I (synCdm G))
          (synWss (synCrn G) (synCdm G))) (.classMem (.cv y) (synCnnc)))
      (.classEq (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      p0304 p0305
  have p0307 :=
    @gEqcomd
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c)))
      (synCfv G (synCfv (synCfrec G I) (.cv y))) p0306
  have p0308 :=
    @gEqeq2d
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (synCfv G (synCfv (synCfrec G I) (.cv y)))
      (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c)))
      (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c))) p0307
  have p0309 :=
    @gMpbidi
      (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv G (synCfv (synCfrec G I) (.cv y))))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0300 p0308
  have p0310 :=
    @gN3expd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
      (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
        (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c))))
      p0309
  have p0312 :=
    @gWppfrecprefixeqvalndv (synCplc (.cv y) (synC1c)) k F G I
      hyp_wpphitprefixtransferpackdndv_1 hyp_wpphitprefixtransferpackdndv_2
      hyp_wpphitprefixtransferpackdndv_3 hyp_wpphitprefixtransferpackdndv_4
      hyp_wpphitprefixtransferpackdndv_5 hyp_wpphitprefixtransferpackdndv_6
  have p0313 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (synWb (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k))
        (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
            (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c))))))
      p0103 p0312
  have p0314 :=
    @gBiimprd (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k))
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c)))))
      p0313
  have p0315 :=
    @gA1d (.classMem (.cv y) (synCnnc))
      (.imp (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
            (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c)))))
        (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k)) p0314
  have p0316 :=
    @gA2d (.classMem (.cv y) (synCnnc))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
          (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c)))))
      (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)) p0315
  have p0317 :=
    @gSylcom
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc))
      (.imp (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (.imp (synWbr (synCplc (.cv y) (synC1c)) (synCkqrel (synClefin)) (.cv k))
          (.classEq (synCfv (synCfrec F I) (synCplc (.cv y) (synC1c)))
            (synCfv (synCfrec G I) (synCplc (.cv y) (synC1c))))))
      (.imp (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)))
      p0310 p0316
  have p0318 :=
    @gAdantrd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc))
      (.imp (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
        (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)))
      synWtru p0317
  have p0319 :=
    @gSyl7bi
      (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      (.classMem (.cv y) (synCwppfrecprefixeq F G I k))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc)) synWtru)
      (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)) p0045 p0318
  have p0320 := @gN1cex
  have p0321 := @gAddcex (.cv y) (synC1c) p0042 p0320
  have p0322 := @gId (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
  have p0323 :=
    @gEleq1d (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.cv x)
      (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k) p0322
  have p0324 :=
    @gElab (.classMem (.cv x) (synCwppfrecprefixeq F G I k))
      (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)) x
      (synCplc (.cv y) (synC1c)) dv_cache_0040 dv_cache_0050 p0321 p0323
  have p0325 :=
    @gBiimpri
      (.classMem (synCplc (.cv y) (synC1c))
        (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k)) p0324
  have p0326 :=
    @gSyl8
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv y) (synCnnc)) synWtru)
      (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      (.classMem (synCplc (.cv y) (synC1c)) (synCwppfrecprefixeq F G I k))
      (.classMem (synCplc (.cv y) (synC1c))
        (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      p0319 p0325
  have p0327 :=
    @gAncomsd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv y) (synCnnc)) synWtru
      (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (.classMem (synCplc (.cv y) (synC1c))
          (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      p0326
  have p0328 :=
    @gExp3a
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru (.classMem (.cv y) (synCnnc))
      (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (.classMem (synCplc (.cv y) (synC1c))
          (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      p0327
  have p0329 :=
    @gRalrimdv
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru
      (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (.classMem (synCplc (.cv y) (synC1c))
          (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      y (synCnnc) dv_cache_0051 dv_cache_0052 p0328
  have p0330 :=
    @g_pm3_2
      (synWa (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
        (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      (synWral y (synCnnc) (.imp
          (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
          (.classMem (synCplc (.cv y) (synC1c))
            (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))))
  have p0331 :=
    @gSyl9
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru
      (synWral y (synCnnc) (.imp
          (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
          (.classMem (synCplc (.cv y) (synC1c))
            (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))))
      (synWa (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
        (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      (synWa (synWa (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))
            (synCvv)) (.classMem (synC0c)
            (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))) (synWral y (synCnnc)
          (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
            (.classMem (synCplc (.cv y) (synC1c))
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))))
      p0329 p0330
  have p0332 :=
    @gSyl5 synWtru
      (synWa (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
        (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.imp synWtru (synWa (synWa
            (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
            (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
          (synWral y (synCnnc) (.imp (.classMem (.cv y)
                (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
              (.classMem (synCplc (.cv y) (synC1c))
                (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))))))
      p0041 p0331
  have p0333 :=
    @gPm243d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru
      (synWa (synWa (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))
            (synCvv)) (.classMem (synC0c)
            (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))) (synWral y (synCnnc)
          (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
            (.classMem (synCplc (.cv y) (synC1c))
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))))
      p0332
  have p0334 :=
    (Nominal.biimpRefl (synW3a
        (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
        (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (synWral y (synCnnc) (.imp (.classMem (.cv y)
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
            (.classMem (synCplc (.cv y) (synC1c))
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))))))
  have p0335 :=
    @gSyl6ibr
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru
      (synWa (synWa (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))
            (synCvv)) (.classMem (synC0c)
            (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))) (synWral y (synCnnc)
          (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
            (.classMem (synCplc (.cv y) (synC1c))
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))))
      (synW3a (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
        (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (synWral y (synCnnc) (.imp (.classMem (.cv y)
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
            (.classMem (synCplc (.cv y) (synC1c))
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))))
      p0333 p0334
  have p0336 :=
    @gPeano5 y (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv)
      dv_cache_0053
  have p0337 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru
      (synW3a (.classMem (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (synCvv))
        (.classMem (synC0c) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (synWral y (synCnnc) (.imp (.classMem (.cv y)
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
            (.classMem (synCplc (.cv y) (synC1c))
              (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))))
      (synWss (synCnnc) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      p0335 p0336
  have p0338 :=
    @gSsel (synCnnc) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))) (.cv n)
  have p0339 :=
    @gSyl6
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru
      (synWss (synCnnc) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      (.imp (.classMem (.cv n) (synCnnc))
        (.classMem (.cv n) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k)))))
      p0337 p0338
  have p0340 :=
    @gCom23
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      synWtru (.classMem (.cv n) (synCnnc))
      (.classMem (.cv n) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      p0339
  have p0341 :=
    @gImp3a
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv n) (synCnnc)) synWtru
      (.classMem (.cv n) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      p0340
  have p0342 := @gId (.classEq (.cv x) (.cv n))
  have p0343 :=
    @gEleq1d (.classEq (.cv x) (.cv n)) (.cv x) (.cv n) (synCwppfrecprefixeq F G I k)
      p0342
  have p0344 :=
    @gElabg (.classMem (.cv x) (synCwppfrecprefixeq F G I k))
      (.classMem (.cv n) (synCwppfrecprefixeq F G I k)) x (.cv n) (synCnnc)
      dv_cache_0054 dv_cache_0055 p0343
  have p0345 :=
    @gAdantr (.classMem (.cv n) (synCnnc))
      (synWb (.classMem (.cv n) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
        (.classMem (.cv n) (synCwppfrecprefixeq F G I k)))
      synWtru p0344
  have p0346 :=
    @gMpbidi (synWa (.classMem (.cv n) (synCnnc)) synWtru)
      (.classMem (.cv n) (.cab x (.classMem (.cv x) (synCwppfrecprefixeq F G I k))))
      (.classMem (.cv n) (synCwppfrecprefixeq F G I k))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0341 p0345
  have p0347 :=
    @gMpan2i
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv n) (synCnnc)) synWtru
      (.classMem (.cv n) (synCwppfrecprefixeq F G I k)) p0016 p0346
  have p0348 :=
    @gWppfrecprefixeqvalndv (.cv n) k F G I hyp_wpphitprefixtransferpackdndv_1
      hyp_wpphitprefixtransferpackdndv_2 hyp_wpphitprefixtransferpackdndv_3
      hyp_wpphitprefixtransferpackdndv_4 hyp_wpphitprefixtransferpackdndv_5
      hyp_wpphitprefixtransferpackdndv_6
  have p0349 :=
    @gMpbidi (.classMem (.cv n) (synCnnc))
      (.classMem (.cv n) (synCwppfrecprefixeq F G I k))
      (.imp (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0347 p0348
  have p0350 :=
    @gRalrimiv
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.imp (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))
      n (synCnnc) dv_cache_0056 p0349
  have p0351 := @gId (.classEq (.cv n) (.cv k))
  have p0352 :=
    @gBreq1d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (.cv k) (synCkqrel (synClefin))
      p0351
  have p0354 := @gFveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (synCfrec F I) p0351
  have p0356 := @gFveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (synCfrec G I) p0351
  have p0357 :=
    @gEqeq12d (.classEq (.cv n) (.cv k)) (synCfv (synCfrec F I) (.cv n))
      (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv n))
      (synCfv (synCfrec G I) (.cv k)) p0354 p0356
  have p0358 :=
    @gImbi12d (.classEq (.cv n) (.cv k))
      (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
      (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n)))
      (.classEq (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k))) p0352
      p0357
  have p0359 :=
    @gRspcv
      (.imp (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n))))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k))))
      n (.cv k) (synCnnc) dv_cache_0057 dv_cache_0058 dv_cache_0059 p0358
  have p0360 :=
    @gSyl5com
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWral n (synCnnc) (.imp (synWbr (.cv n) (synCkqrel (synClefin)) (.cv k))
          (.classEq (synCfv (synCfrec F I) (.cv n)) (synCfv (synCfrec G I) (.cv n)))))
      (.classMem (.cv k) (synCnnc))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k))))
      p0350 p0359
  have p0361 :=
    @gMpd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCnnc))
      (.imp (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
        (.classEq (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k))))
      p0000 p0360
  have p0362 :=
    @gMpd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv k))
      (.classEq (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k))) p0015
      p0361
  have p0363 :=
    @gEqcomd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synCfv (synCfrec F I) (.cv k)) (synCfv (synCfrec G I) (.cv k)) p0362
  have p0364 :=
    @gBreq2d
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synCfv (synCfrec G I) (.cv k)) (synCfv (synCfrec F I) (.cv k)) L (synClec)
      p0363
  have p0365 :=
    @gMpbid
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWbr L (synClec) (synCfv (synCfrec G I) (.cv k)))
      (synWbr L (synClec) (synCfv (synCfrec F I) (.cv k))) p0008 p0364
  have p0366 :=
    @gJca
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec F I) (.cv k))) p0000 p0365
  have p0368 := @gElwpphitvndv L F I (.cv k)
  have p0369 := Nominal.mp p0022 p0368
  have p0370 :=
    @gSylibr
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F I) (.cv k))))
      (.classMem (.cv k) (synCwpphit F I L)) p0366 p0369
  have p0371 :=
    @gJca
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G I L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G I L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCwpphit F I L))
      (.classEq (synCfv (synCfrec G I) (.cv k)) (synCfv (synCfrec F I) (.cv k))) p0370
      p0363
  exact p0371


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part060`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppreachprefixbidv`. -/
@[expose]
noncomputable def gWppreachprefixbidv (D : Class) (F : Class) (G : Class) (L : Class)
    (q : Var) (dv_D_q : q ∉ D.fv) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv)
    (dv_L_q : q ∉ L.fv)
    (hyp_wppreachprefixbidv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachprefixbidv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachprefixbidv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachprefixbidv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppreachprefixbidv_5 : Nominal.NPrf (.classMem D (synCdm G)))
    (hyp_wppreachprefixbidv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppreachprefixbidv_7 : Nominal.NPrf (.classMem L (synCvv)))
    (hyp_wppreachprefixbidv_8 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F D) (.cv q))))
            (synWbr (synCfv (synCfrec F D) (.cv q)) (synClec) L))))
    (hyp_wppreachprefixbidv_9 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec F D) (.cv q)) (synClec) L)
            (.classEq (synCfv G (synCfv (synCfrec F D) (.cv q)))
              (synCfv F (synCfv (synCfrec F D) (.cv q)))))))
    (hyp_wppreachprefixbidv_10 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G D) (.cv q))))
            (synWbr (synCfv (synCfrec G D) (.cv q)) (synClec) L))))
    (hyp_wppreachprefixbidv_11 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec G D) (.cv q)) (synClec) L)
            (.classEq (synCfv F (synCfv (synCfrec G D) (.cv q)))
              (synCfv G (synCfv (synCfrec G D) (.cv q))))))) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppreach F L)) (.classMem D (synCwppreach G L))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ F.fv ∪ G.fv ∪ L.fv ∪ ({ q } : Finset Var)
  let n : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_L : n ∉ L.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_D : k ∉ D.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_L : k ∉ L.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_ne_q : k ≠ q := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_G : r ∉ G.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_L : r ∉ L.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_q : r ≠ q := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_r : q ≠ r := Ne.symm fresh_r_ne_q
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_r : n ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_n : r ≠ n := Ne.symm fresh_n_ne_r
  have fresh_k_ne_r : k ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : n ∉ (L).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_L, not_false_eq_true])
  have dv_cache_0002 : n ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_D, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_F, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((Wff.classMem (.cv n) (synCwpphit F D L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_L, fresh_r_not_F, fresh_r_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem (.cv r) (synCwpphit F D L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L, fresh_n_not_F, fresh_n_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0008 :
    n ∉ ((synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit F D L)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L,
          fresh_n_not_F, fresh_n_not_D, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 : k ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_L, not_false_eq_true])
  have dv_cache_0010 : q ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_q, not_false_eq_true])
  have dv_cache_0011 : r ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_L, not_false_eq_true])
  have dv_cache_0012 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0013 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_q, not_false_eq_true])
  have dv_cache_0014 : r ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_F, not_false_eq_true])
  have dv_cache_0015 : k ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_D, not_false_eq_true])
  have dv_cache_0016 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0017 : r ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_D, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0020 : r ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0021 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show k ≠ q from (by exact fresh_k_ne_q))
  have dv_cache_0022 : k ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show k ≠ r from (by exact fresh_k_ne_r))
  have dv_cache_0023 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0024 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_q, not_false_eq_true])
  have dv_cache_0025 : k ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0026 :
    n ∉ ((synWbr L (synClec) (synCfv (synCfrec G D) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_not_L, fresh_n_ne_k, fresh_n_not_G, fresh_n_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 :
    k ∉ ((synWbr L (synClec) (synCfv (synCfrec G D) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_G, fresh_k_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0028 :
    k ∉
      ((synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_G, fresh_k_not_D,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0029 : n ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_G, not_false_eq_true])
  have dv_cache_0030 : r ∉ ((Wff.classMem (.cv n) (synCwpphit G D L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_L, fresh_r_not_G, fresh_r_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0031 : n ∉ ((Wff.classMem (.cv r) (synCwpphit G D L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L, fresh_n_not_G, fresh_n_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0032 :
    n ∉ ((synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit G D L)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_r, fresh_n_not_L,
          fresh_n_not_G, fresh_n_not_D, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0033 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_G, not_false_eq_true])
  have dv_cache_0034 : r ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_G, not_false_eq_true])
  have dv_cache_0035 :
    n ∉ ((synWbr L (synClec) (synCfv (synCfrec F D) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_not_L, fresh_n_ne_k, fresh_n_not_F, fresh_n_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0036 :
    k ∉ ((synWbr L (synClec) (synCfv (synCfrec F D) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_F, fresh_k_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0037 :
    k ∉
      ((synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))).fv :=
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
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_k_not_L, fresh_k_ne_n, fresh_k_not_F, fresh_k_not_D,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gWppreachfwdrexvndv L D n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2 hyp_wppreachprefixbidv_3
      hyp_wppreachprefixbidv_7
  have p0001 :=
    @gBiimpi (.classMem D (synCwppreach F L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0000
  have p0002 := @gFinlewe
  have p0003 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0002
  have p0004 :=
    @gSimpl (.classMem (.cv n) (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n)))
  have p0005 :=
    @gN3pm32i (.classMem F (synCfuns)) (.classMem D (synCdm F))
      (synWss (synCrn F) (synCdm F)) hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2
      hyp_wppreachprefixbidv_3
  have p0006 := @gElwpphitvndv L F D (.cv n)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gBiimpri (.classMem (.cv n) (synCwpphit F D L))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0007
  have p0009 :=
    @gJca
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpphit F D L)) p0004 p0008
  have p0010 := @gRspe (.classMem (.cv n) (synCwpphit F D L)) n (synCnnc)
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWa (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpphit F D L)))
      (synWrex n (synCnnc) (.classMem (.cv n) (synCwpphit F D L))) p0009 p0010
  have p0012 := @gId (.classEq (.cv n) (.cv r))
  have p0013 :=
    @gEleq1d (.classEq (.cv n) (.cv r)) (.cv n) (.cv r) (synCwpphit F D L) p0012
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n r) (synWb (.classMem (.cv n) (synCwpphit F D L))
          (.classMem (.cv r) (synCwpphit F D L)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gCbvrexv (.classMem (.cv n) (synCwpphit F D L))
      (.classMem (.cv r) (synCwpphit F D L)) n r (synCnnc) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0014_e00_recanon
  have p0015 :=
    @gBiimpi (synWrex n (synCnnc) (.classMem (.cv n) (synCwpphit F D L)))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit F D L))) p0014
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWrex n (synCnnc) (.classMem (.cv n) (synCwpphit F D L)))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit F D L))) p0011 p0015
  have p0017 :=
    @gRexlimiva (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n)))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit F D L))) n (synCnnc)
      dv_cache_0008 p0016
  have p0018 :=
    @gJca
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit F D L))) p0003 p0017
  have p0019 := @gElex F (synCfuns)
  have p0020 := Nominal.mp hyp_wppreachprefixbidv_1 p0019
  have p0021 :=
    @gWpphitminexvndv r L (synCkqrel (synClefin)) k q F D dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 p0020
  have p0022 :=
    @gSyl
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWa (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
        (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit F D L))))
      (synWrex k (synCnnc) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0018 p0021
  have p0023 :=
    @gWpphitprefixtransferpackdndv k G F D L q dv_cache_0024 dv_cache_0013 dv_cache_0016
      dv_cache_0010 dv_cache_0021 hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5
      hyp_wppreachprefixbidv_6 hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2
      hyp_wppreachprefixbidv_3 hyp_wppreachprefixbidv_8 hyp_wppreachprefixbidv_9
  have p0024 :=
    @gSimpl (.classMem (.cv k) (synCwpphit G D L))
      (.classEq (synCfv (synCfrec F D) (.cv k)) (synCfv (synCfrec G D) (.cv k)))
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCwpphit G D L))
        (.classEq (synCfv (synCfrec F D) (.cv k)) (synCfv (synCfrec G D) (.cv k))))
      (.classMem (.cv k) (synCwpphit G D L)) p0023 p0024
  have p0026 :=
    @gN3pm32i (.classMem G (synCfuns)) (.classMem D (synCdm G))
      (synWss (synCrn G) (synCdm G)) hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5
      hyp_wppreachprefixbidv_6
  have p0027 := @gElwpphitvndv L G D (.cv k)
  have p0028 := Nominal.mp p0026 p0027
  have p0029 :=
    @gA1i
      (synWb (.classMem (.cv k) (synCwpphit G D L)) (synWa (.classMem (.cv k) (synCnnc))
          (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k)))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0028
  have p0030 :=
    @gBiimpd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCwpphit G D L))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))))
      p0029
  have p0031 :=
    @gMpd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCwpphit G D L))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))))
      p0025 p0030
  have p0032 :=
    @gRspe (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))) k (synCnnc)
  have p0033 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))))
      (synWrex k (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))))
      p0031 p0032
  have p0034 := @gId (.classEq (.cv k) (.cv n))
  have p0035 := @gFveq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (synCfrec G D) p0034
  have p0036 :=
    @gBreq2d (.classEq (.cv k) (.cv n)) (synCfv (synCfrec G D) (.cv k))
      (synCfv (synCfrec G D) (.cv n)) L (synClec) p0035
  have p0037_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k n) (synWb (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k)))
          (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synClec synCopab synCfv synCio synCuni synCsn synCfrec
          synCclos1 synCint synCpprod synCtxp synCin synCcom synCcnv synC1st
          synCmpt synCvv synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0037 :=
    @gCbvrexv (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k)))
      (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))) k n (synCnnc)
      dv_cache_0025 dv_cache_0004 dv_cache_0026 dv_cache_0027 p0037_e00_recanon
  have p0038 :=
    @gBiimpi
      (synWrex k (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0037
  have p0039 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWrex k (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv k))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0033 p0038
  have p0040 :=
    @gRexlimiva
      (synWa (.classMem (.cv k) (synCwpphit F D L)) (synWral q (synCnnc)
          (.imp (.classMem (.cv q) (synCwpphit F D L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n)))) k
      (synCnnc) dv_cache_0028 p0039
  have p0041 :=
    @gSyl
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWrex k (synCnnc) (synWa (.classMem (.cv k) (synCwpphit F D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit F D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0022 p0040
  have p0042 :=
    @gSyl (.classMem D (synCwppreach F L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0001 p0041
  have p0043 :=
    @gWppreachfwdrexvndv L D n G dv_cache_0001 dv_cache_0002 dv_cache_0029
      hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5 hyp_wppreachprefixbidv_6
      hyp_wppreachprefixbidv_7
  have p0044 :=
    @gBiimpri (.classMem D (synCwppreach G L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0043
  have p0045 :=
    @gSyl (.classMem D (synCwppreach F L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (.classMem D (synCwppreach G L)) p0042 p0044
  have p0047 :=
    @gBiimpi (.classMem D (synCwppreach G L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0043
  have p0049 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0002
  have p0050 :=
    @gSimpl (.classMem (.cv n) (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n)))
  have p0052 := @gElwpphitvndv L G D (.cv n)
  have p0053 := Nominal.mp p0026 p0052
  have p0054 :=
    @gBiimpri (.classMem (.cv n) (synCwpphit G D L))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      p0053
  have p0055 :=
    @gJca
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpphit G D L)) p0050 p0054
  have p0056 := @gRspe (.classMem (.cv n) (synCwpphit G D L)) n (synCnnc)
  have p0057 :=
    @gSyl
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (synWa (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCwpphit G D L)))
      (synWrex n (synCnnc) (.classMem (.cv n) (synCwpphit G D L))) p0055 p0056
  have p0058 := @gId (.classEq (.cv n) (.cv r))
  have p0059 :=
    @gEleq1d (.classEq (.cv n) (.cv r)) (.cv n) (.cv r) (synCwpphit G D L) p0058
  have p0060_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n r) (synWb (.classMem (.cv n) (synCwpphit G D L))
          (.classMem (.cv r) (synCwpphit G D L)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0059
  have p0060 :=
    @gCbvrexv (.classMem (.cv n) (synCwpphit G D L))
      (.classMem (.cv r) (synCwpphit G D L)) n r (synCnnc) dv_cache_0004 dv_cache_0005
      dv_cache_0030 dv_cache_0031 p0060_e00_recanon
  have p0061 :=
    @gBiimpi (synWrex n (synCnnc) (.classMem (.cv n) (synCwpphit G D L)))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit G D L))) p0060
  have p0062 :=
    @gSyl
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (synWrex n (synCnnc) (.classMem (.cv n) (synCwpphit G D L)))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit G D L))) p0057 p0061
  have p0063 :=
    @gRexlimiva (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n)))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit G D L))) n (synCnnc)
      dv_cache_0032 p0062
  have p0064 :=
    @gJca
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit G D L))) p0049 p0063
  have p0065 := @gElex G (synCfuns)
  have p0066 := Nominal.mp hyp_wppreachprefixbidv_4 p0065
  have p0067 :=
    @gWpphitminexvndv r L (synCkqrel (synClefin)) k q G D dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0033 dv_cache_0024 dv_cache_0034 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 p0066
  have p0068 :=
    @gSyl
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (synWa (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
        (synWrex r (synCnnc) (.classMem (.cv r) (synCwpphit G D L))))
      (synWrex k (synCnnc) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0064 p0067
  have p0069 :=
    @gWpphitprefixtransferpackdndv k F G D L q dv_cache_0013 dv_cache_0024 dv_cache_0016
      dv_cache_0010 dv_cache_0021 hyp_wppreachprefixbidv_1 hyp_wppreachprefixbidv_2
      hyp_wppreachprefixbidv_3 hyp_wppreachprefixbidv_4 hyp_wppreachprefixbidv_5
      hyp_wppreachprefixbidv_6 hyp_wppreachprefixbidv_10 hyp_wppreachprefixbidv_11
  have p0070 :=
    @gSimpl (.classMem (.cv k) (synCwpphit F D L))
      (.classEq (synCfv (synCfrec G D) (.cv k)) (synCfv (synCfrec F D) (.cv k)))
  have p0071 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCwpphit F D L))
        (.classEq (synCfv (synCfrec G D) (.cv k)) (synCfv (synCfrec F D) (.cv k))))
      (.classMem (.cv k) (synCwpphit F D L)) p0069 p0070
  have p0073 := @gElwpphitvndv L F D (.cv k)
  have p0074 := Nominal.mp p0005 p0073
  have p0075 :=
    @gA1i
      (synWb (.classMem (.cv k) (synCwpphit F D L)) (synWa (.classMem (.cv k) (synCnnc))
          (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k)))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      p0074
  have p0076 :=
    @gBiimpd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCwpphit F D L))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))))
      p0075
  have p0077 :=
    @gMpd
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (.classMem (.cv k) (synCwpphit F D L))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))))
      p0071 p0076
  have p0078 :=
    @gRspe (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))) k (synCnnc)
  have p0079 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))))
      (synWrex k (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))))
      p0077 p0078
  have p0080 := @gId (.classEq (.cv k) (.cv n))
  have p0081 := @gFveq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (synCfrec F D) p0080
  have p0082 :=
    @gBreq2d (.classEq (.cv k) (.cv n)) (synCfv (synCfrec F D) (.cv k))
      (synCfv (synCfrec F D) (.cv n)) L (synClec) p0081
  have p0083_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k n) (synWb (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k)))
          (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synClec synCopab synCfv synCio synCuni synCsn synCfrec
          synCclos1 synCint synCpprod synCtxp synCin synCcom synCcnv synC1st
          synCmpt synCvv synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0082
  have p0083 :=
    @gCbvrexv (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k)))
      (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))) k n (synCnnc)
      dv_cache_0025 dv_cache_0004 dv_cache_0035 dv_cache_0036 p0083_e00_recanon
  have p0084 :=
    @gBiimpi
      (synWrex k (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0083
  have p0085 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWrex k (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv k))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0079 p0084
  have p0086 :=
    @gRexlimiva
      (synWa (.classMem (.cv k) (synCwpphit G D L)) (synWral q (synCnnc)
          (.imp (.classMem (.cv q) (synCwpphit G D L))
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q)))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n)))) k
      (synCnnc) dv_cache_0037 p0085
  have p0087 :=
    @gSyl
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (synWrex k (synCnnc) (synWa (.classMem (.cv k) (synCwpphit G D L))
          (synWral q (synCnnc) (.imp (.classMem (.cv q) (synCwpphit G D L))
              (synWbr (.cv k) (synCkqrel (synClefin)) (.cv q))))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0068 p0086
  have p0088 :=
    @gSyl (.classMem D (synCwppreach G L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec G D) (.cv n))))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0047 p0087
  have p0090 :=
    @gBiimpri (.classMem D (synCwppreach F L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0000
  have p0091 :=
    @gSyl (.classMem D (synCwppreach G L))
      (synWrex n (synCnnc) (synWbr L (synClec) (synCfv (synCfrec F D) (.cv n))))
      (.classMem D (synCwppreach F L)) p0088 p0090
  have p0092 :=
    @gImpbii (.classMem D (synCwppreach F L)) (.classMem D (synCwppreach G L)) p0045
      p0091
  exact p0092


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part061`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppcandprefixpointbidv`. -/
@[expose]
noncomputable def gWppcandprefixpointbidv (D : Class) (F : Class) (G : Class) (L : Class)
    (q : Var) (dv_D_q : q ∉ D.fv) (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv)
    (dv_L_q : q ∉ L.fv)
    (hyp_wppcandprefixpointbidv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppcandprefixpointbidv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppcandprefixpointbidv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppcandprefixpointbidv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppcandprefixpointbidv_5 : Nominal.NPrf (.classMem D (synCdm G)))
    (hyp_wppcandprefixpointbidv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppcandprefixpointbidv_7 : Nominal.NPrf (.classMem L (synCvv)))
    (hyp_wppcandprefixpointbidv_8 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec F D) (.cv q))))
            (synWbr (synCfv (synCfrec F D) (.cv q)) (synClec) L))))
    (hyp_wppcandprefixpointbidv_9 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec F D) (.cv q)) (synClec) L)
            (.classEq (synCfv G (synCfv (synCfrec F D) (.cv q)))
              (synCfv F (synCfv (synCfrec F D) (.cv q)))))))
    (hyp_wppcandprefixpointbidv_10 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (.neg (synWbr L (synClec) (synCfv (synCfrec G D) (.cv q))))
            (synWbr (synCfv (synCfrec G D) (.cv q)) (synClec) L))))
    (hyp_wppcandprefixpointbidv_11 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec G D) (.cv q)) (synClec) L)
            (.classEq (synCfv F (synCfv (synCfrec G D) (.cv q)))
              (synCfv G (synCfv (synCfrec G D) (.cv q))))))) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppcand F L)) (.classMem D (synCwppcand G L))) :=
  by
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0002 : q ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_q, not_false_eq_true])
  have dv_cache_0003 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_q, not_false_eq_true])
  have dv_cache_0004 : q ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_q, not_false_eq_true])
  have p0000 := @gElwppcand L D F
  have p0001 :=
    @gBiid (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
  have p0002 :=
    @gWppreachprefixbidv D F G L q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_wppcandprefixpointbidv_1 hyp_wppcandprefixpointbidv_2
      hyp_wppcandprefixpointbidv_3 hyp_wppcandprefixpointbidv_4
      hyp_wppcandprefixpointbidv_5 hyp_wppcandprefixpointbidv_6
      hyp_wppcandprefixpointbidv_7 hyp_wppcandprefixpointbidv_8
      hyp_wppcandprefixpointbidv_9 hyp_wppcandprefixpointbidv_10
      hyp_wppcandprefixpointbidv_11
  have p0003 :=
    @gAnbi12i (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
      (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
      (.classMem D (synCwppreach F L)) (.classMem D (synCwppreach G L)) p0001 p0002
  have p0004 :=
    @gBitri (.classMem D (synCwppcand F L))
      (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
        (.classMem D (synCwppreach F L)))
      (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
        (.classMem D (synCwppreach G L)))
      p0000 p0003
  have p0005 := @gElwppcand L D G
  have p0006 :=
    @gBicomi (.classMem D (synCwppcand G L))
      (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
        (.classMem D (synCwppreach G L)))
      p0005
  have p0007 :=
    @gBitri (.classMem D (synCwppcand F L))
      (synWa (synWa (.classMem D (synChwcards (synCvv))) (synWbr D (synClec) L))
        (.classMem D (synCwppreach G L)))
      (.classMem D (synCwppcand G L)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppgammaprefixeqpointndv`. -/
@[expose]
noncomputable def gWppgammaprefixeqpointndv (F : Class) (G : Class) (L : Class) (q : Var)
    (dv_F_q : q ∉ F.fv) (dv_G_q : q ∉ G.fv) (dv_L_q : q ∉ L.fv)
    (hyp_wppgammaprefixeqpointndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppgammaprefixeqpointndv_2 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppgammaprefixeqpointndv_3 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppgammaprefixeqpointndv_4 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppgammaprefixeqpointndv_5 : Nominal.NPrf (.classMem L (synChwcards (synCvv))))
    (hyp_wppgammaprefixeqpointndv_6 : Nominal.NPrf (.classMem (synCwppgamma F L) (synCdm F)))
    (hyp_wppgammaprefixeqpointndv_7 : Nominal.NPrf (.classMem (synCwppgamma F L) (synCdm G)))
    (hyp_wppgammaprefixeqpointndv_8 : Nominal.NPrf (synWral q (synCnnc) (.imp (.neg
              (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma F L)) (.cv q))))
            (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L))))
    (hyp_wppgammaprefixeqpointndv_9 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)) (synClec) L)
            (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))
              (synCfv F (synCfv (synCfrec F (synCwppgamma F L)) (.cv q)))))))
    (hyp_wppgammaprefixeqpointndv_10 : Nominal.NPrf (synWral q (synCnnc) (.imp (.neg
              (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma F L)) (.cv q))))
            (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L))))
    (hyp_wppgammaprefixeqpointndv_11 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)) (synClec) L)
            (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))
              (synCfv G (synCfv (synCfrec G (synCwppgamma F L)) (.cv q)))))))
    (hyp_wppgammaprefixeqpointndv_12 : Nominal.NPrf (.classMem (synCwppgamma G L) (synCdm F)))
    (hyp_wppgammaprefixeqpointndv_13 : Nominal.NPrf (.classMem (synCwppgamma G L) (synCdm G)))
    (hyp_wppgammaprefixeqpointndv_14 : Nominal.NPrf (synWral q (synCnnc) (.imp (.neg
              (synWbr L (synClec) (synCfv (synCfrec F (synCwppgamma G L)) (.cv q))))
            (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L))))
    (hyp_wppgammaprefixeqpointndv_15 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)) (synClec) L)
            (.classEq (synCfv G (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))
              (synCfv F (synCfv (synCfrec F (synCwppgamma G L)) (.cv q)))))))
    (hyp_wppgammaprefixeqpointndv_16 : Nominal.NPrf (synWral q (synCnnc) (.imp (.neg
              (synWbr L (synClec) (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))
            (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L))))
    (hyp_wppgammaprefixeqpointndv_17 : Nominal.NPrf (synWral q (synCnnc)
          (.imp (synWbr (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)) (synClec) L)
            (.classEq (synCfv F (synCfv (synCfrec G (synCwppgamma G L)) (.cv q)))
              (synCfv G (synCfv (synCfrec G (synCwppgamma G L)) (.cv q))))))) :
    Nominal.NPrf (.classEq (synCwppgamma F L) (synCwppgamma G L)) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ L.fv ∪ ({ q } : Finset Var)
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_L : k ∉ L.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : k ∉ (L).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_L, not_false_eq_true])
  have dv_cache_0002 : k ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have dv_cache_0003 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_G, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((synCwppgamma G L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_L_q, dv_G_q, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_q, not_false_eq_true])
  have dv_cache_0006 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_q, not_false_eq_true])
  have dv_cache_0007 : q ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_L_q, not_false_eq_true])
  have dv_cache_0008 : k ∉ ((synCwppgamma G L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_k_not_L, fresh_k_not_G, or_false, not_false_eq_true])
  have dv_cache_0009 : k ∉ ((synCwppcand F L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, fresh_k_not_L, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0010 :
    k ∉ ((synWbr (synCwppgamma F L) (synClec) (synCwppgamma G L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_k_not_L, fresh_k_not_F, fresh_k_not_G, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : q ∉ ((synCwppgamma F L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_L_q, dv_F_q, or_false, not_false_eq_true])
  have dv_cache_0012 : k ∉ ((synCwppgamma F L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_k_not_L, fresh_k_not_F, or_false, not_false_eq_true])
  have dv_cache_0013 : k ∉ ((synCwppcand G L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, fresh_k_not_L, fresh_k_not_G, or_false, not_false_eq_true])
  have dv_cache_0014 :
    k ∉ ((synWbr (synCwppgamma G L) (synClec) (synCwppgamma F L))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_k_not_L, fresh_k_not_G, fresh_k_not_F, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wppgammaprefixeqpointndv_1 p0000
  have p0002 :=
    @gPm32i (.classMem F (synCvv)) (.classMem L (synChwcards (synCvv))) p0001
      hyp_wppgammaprefixeqpointndv_5
  have p0003 := @gWppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gSimpr (.classMem (synCwppgamma F L) (synCwppcand F L))
      (synWral k (synCwppcand F L) (synWbr (synCwppgamma F L) (synClec) (.cv k)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gElex G (synCfuns)
  have p0008 := Nominal.mp hyp_wppgammaprefixeqpointndv_3 p0007
  have p0009 :=
    @gPm32i (.classMem G (synCvv)) (.classMem L (synChwcards (synCvv))) p0008
      hyp_wppgammaprefixeqpointndv_5
  have p0010 := @gWppgammaminhwndv L k G dv_cache_0001 dv_cache_0003
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gSimpl (.classMem (synCwppgamma G L) (synCwppcand G L))
      (synWral k (synCwppcand G L) (synWbr (synCwppgamma G L) (synClec) (.cv k)))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gElex L (synChwcards (synCvv))
  have p0015 := Nominal.mp hyp_wppgammaprefixeqpointndv_5 p0014
  have p0016 :=
    @gWppcandprefixpointbidv (synCwppgamma G L) F G L q dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 hyp_wppgammaprefixeqpointndv_1
      hyp_wppgammaprefixeqpointndv_12 hyp_wppgammaprefixeqpointndv_2
      hyp_wppgammaprefixeqpointndv_3 hyp_wppgammaprefixeqpointndv_13
      hyp_wppgammaprefixeqpointndv_4 p0015 hyp_wppgammaprefixeqpointndv_14
      hyp_wppgammaprefixeqpointndv_15 hyp_wppgammaprefixeqpointndv_16
      hyp_wppgammaprefixeqpointndv_17
  have p0017 :=
    @gMpbir (.classMem (synCwppgamma G L) (synCwppcand F L))
      (.classMem (synCwppgamma G L) (synCwppcand G L)) p0013 p0016
  have p0018 := @gId (.classEq (.cv k) (synCwppgamma G L))
  have p0019 :=
    @gBreq2d (.classEq (.cv k) (synCwppgamma G L)) (.cv k) (synCwppgamma G L)
      (synCwppgamma F L) (synClec) p0018
  have p0020 :=
    @gRspcv (synWbr (synCwppgamma F L) (synClec) (.cv k))
      (synWbr (synCwppgamma F L) (synClec) (synCwppgamma G L)) k (synCwppgamma G L)
      (synCwppcand F L) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0019
  have p0021 := Nominal.mp p0017 p0020
  have p0022 := Nominal.mp p0006 p0021
  have p0028 :=
    @gSimpr (.classMem (synCwppgamma G L) (synCwppcand G L))
      (synWral k (synCwppcand G L) (synWbr (synCwppgamma G L) (synClec) (.cv k)))
  have p0029 := Nominal.mp p0011 p0028
  have p0035 :=
    @gSimpl (.classMem (synCwppgamma F L) (synCwppcand F L))
      (synWral k (synCwppcand F L) (synWbr (synCwppgamma F L) (synClec) (.cv k)))
  have p0036 := Nominal.mp p0004 p0035
  have p0039 :=
    @gWppcandprefixpointbidv (synCwppgamma F L) F G L q dv_cache_0011 dv_cache_0005
      dv_cache_0006 dv_cache_0007 hyp_wppgammaprefixeqpointndv_1
      hyp_wppgammaprefixeqpointndv_6 hyp_wppgammaprefixeqpointndv_2
      hyp_wppgammaprefixeqpointndv_3 hyp_wppgammaprefixeqpointndv_7
      hyp_wppgammaprefixeqpointndv_4 p0015 hyp_wppgammaprefixeqpointndv_8
      hyp_wppgammaprefixeqpointndv_9 hyp_wppgammaprefixeqpointndv_10
      hyp_wppgammaprefixeqpointndv_11
  have p0040 :=
    @gMpbi (.classMem (synCwppgamma F L) (synCwppcand F L))
      (.classMem (synCwppgamma F L) (synCwppcand G L)) p0036 p0039
  have p0041 := @gId (.classEq (.cv k) (synCwppgamma F L))
  have p0042 :=
    @gBreq2d (.classEq (.cv k) (synCwppgamma F L)) (.cv k) (synCwppgamma F L)
      (synCwppgamma G L) (synClec) p0041
  have p0043 :=
    @gRspcv (synWbr (synCwppgamma G L) (synClec) (.cv k))
      (synWbr (synCwppgamma G L) (synClec) (synCwppgamma F L)) k (synCwppgamma F L)
      (synCwppcand G L) dv_cache_0012 dv_cache_0013 dv_cache_0014 p0042
  have p0044 := Nominal.mp p0040 p0043
  have p0045 := Nominal.mp p0029 p0044
  have p0046 :=
    @gPm32i (synWbr (synCwppgamma F L) (synClec) (synCwppgamma G L))
      (synWbr (synCwppgamma G L) (synClec) (synCwppgamma F L)) p0022 p0045
  have p0054 := @gElwppcand L (synCwppgamma F L) F
  have p0055 :=
    @gMpbi (.classMem (synCwppgamma F L) (synCwppcand F L))
      (synWa (synWa (.classMem (synCwppgamma F L) (synChwcards (synCvv)))
          (synWbr (synCwppgamma F L) (synClec) L))
        (.classMem (synCwppgamma F L) (synCwppreach F L)))
      p0036 p0054
  have p0056 :=
    @gSimpl
      (synWa (.classMem (synCwppgamma F L) (synChwcards (synCvv)))
        (synWbr (synCwppgamma F L) (synClec) L))
      (.classMem (synCwppgamma F L) (synCwppreach F L))
  have p0057 := Nominal.mp p0055 p0056
  have p0058 :=
    @gSimpl (.classMem (synCwppgamma F L) (synChwcards (synCvv)))
      (synWbr (synCwppgamma F L) (synClec) L)
  have p0059 := Nominal.mp p0057 p0058
  have p0060 := @gHwcardssnc (synCvv)
  have p0061 := @gSseli (synChwcards (synCvv)) (synCncs) (synCwppgamma F L) p0060
  have p0062 := Nominal.mp p0059 p0061
  have p0070 := @gElwppcand L (synCwppgamma G L) G
  have p0071 :=
    @gMpbi (.classMem (synCwppgamma G L) (synCwppcand G L))
      (synWa (synWa (.classMem (synCwppgamma G L) (synChwcards (synCvv)))
          (synWbr (synCwppgamma G L) (synClec) L))
        (.classMem (synCwppgamma G L) (synCwppreach G L)))
      p0013 p0070
  have p0072 :=
    @gSimpl
      (synWa (.classMem (synCwppgamma G L) (synChwcards (synCvv)))
        (synWbr (synCwppgamma G L) (synClec) L))
      (.classMem (synCwppgamma G L) (synCwppreach G L))
  have p0073 := Nominal.mp p0071 p0072
  have p0074 :=
    @gSimpl (.classMem (synCwppgamma G L) (synChwcards (synCvv)))
      (synWbr (synCwppgamma G L) (synClec) L)
  have p0075 := Nominal.mp p0073 p0074
  have p0077 := @gSseli (synChwcards (synCvv)) (synCncs) (synCwppgamma G L) p0060
  have p0078 := Nominal.mp p0075 p0077
  have p0079 :=
    @gPm32i (.classMem (synCwppgamma F L) (synCncs))
      (.classMem (synCwppgamma G L) (synCncs)) p0062 p0078
  have p0080 := @gSbth (synCwppgamma F L) (synCwppgamma G L)
  have p0081 := Nominal.mp p0079 p0080
  have p0082 := Nominal.mp p0046 p0081
  exact p0082

/-- Checked nominal proof certificate identified upstream as `g_wecomparisonnclecclndv`. -/
@[expose]
noncomputable def gWecomparisonnclecclndv (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecomparisonnclecclndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecomparisonnclecclndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (synWo (synWbr (synCnc D) (synClec) (synCnc E))
        (synWbr (synCnc E) (synClec) (synCnc D))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let h : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_h_ne_x : h ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : h ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : h ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : h ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : h ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_S, not_false_eq_true])
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
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have p0000 :=
    @gWecomparisonterminalfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisonnclecclndv_1 hyp_wecomparisonnclecclndv_2
  have p0001 :=
    @gOrc (synWex h (synWiso (.cv h) R S D E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
  have p0002 :=
    @gWecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisonnclecclndv_2
  have p0003 :=
    @gSyl (synWex h (synWiso (.cv h) R S D E))
      (synWo (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (synWbr (synCnc D) (synClec) (synCnc E)) p0001 p0002
  have p0004 :=
    @gOrc (synWbr (synCnc D) (synClec) (synCnc E))
      (synWbr (synCnc E) (synClec) (synCnc D))
  have p0005 :=
    @gSyl (synWex h (synWiso (.cv h) R S D E))
      (synWbr (synCnc D) (synClec) (synCnc E))
      (synWo (synWbr (synCnc D) (synClec) (synCnc E))
        (synWbr (synCnc E) (synClec) (synCnc D)))
      p0003 p0004
  have p0006 :=
    @gOlc
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) R S D E))
  have p0008 :=
    @gSyl
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWo (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (synWbr (synCnc D) (synClec) (synCnc E)) p0006 p0002
  have p0010 :=
    @gSyl
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWbr (synCnc D) (synClec) (synCnc E))
      (synWo (synWbr (synCnc D) (synClec) (synCnc E))
        (synWbr (synCnc E) (synClec) (synCnc D)))
      p0008 p0004
  have p0011 :=
    @gOlc
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) S R E D))
  have p0012 :=
    @gWecomparisonforwardnclecclfdv x E S R h D dv_cache_0003 dv_cache_0004 dv_cache_0001
      dv_cache_0002 dv_cache_0007 dv_cache_0008 dv_cache_0005 dv_cache_0006 dv_cache_0009
      hyp_wecomparisonnclecclndv_1
  have p0013 :=
    @gSyl
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWo (synWex h (synWiso (.cv h) S R E D)) (synWrex x D (synWex h
            (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWbr (synCnc E) (synClec) (synCnc D)) p0011 p0012
  have p0014 :=
    @gOlc (synWbr (synCnc E) (synClec) (synCnc D))
      (synWbr (synCnc D) (synClec) (synCnc E))
  have p0015 :=
    @gSyl
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWbr (synCnc E) (synClec) (synCnc D))
      (synWo (synWbr (synCnc D) (synClec) (synCnc E))
        (synWbr (synCnc E) (synClec) (synCnc D)))
      p0013 p0014
  have p0016 :=
    @gN3jaoi (synWex h (synWiso (.cv h) R S D E))
      (synWo (synWbr (synCnc D) (synClec) (synCnc E))
        (synWbr (synCnc E) (synClec) (synCnc D)))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0005 p0010 p0015
  have p0017 := Nominal.mp p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wecomparisonnclecandndv`. -/
@[expose]
noncomputable def gWecomparisonnclecandndv (e : Var) (s : Var) (r : Var) (d : Var) :
    Nominal.NPrf
      (.imp (synWa (synWbr (.cv r) (synCwe) (.cv d)) (synWbr (.cv s) (synCwe) (.cv e)))
        (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
          (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))))) :=
  by
  have p0000 :=
    @gBiid
      (.imp (synWbr (.cv r) (synCwe) (.cv d))
        (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
          (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d)))))
  have p0001 :=
    @gA1i
      (synWb (.imp (synWbr (.cv r) (synCwe) (.cv d))
          (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
            (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d)))))
        (.imp (synWbr (.cv r) (synCwe) (.cv d))
          (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
            (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))))))
      (.classEq (.cv s)
        (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin))))
      p0000
  have p0002 :=
    @gId
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
  have p0003 :=
    @gNceqd
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)) p0002
  have p0004 :=
    @gBreq2d
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synCnc (.cv e))
      (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synCnc (.cv d)) (synClec) p0003
  have p0007 :=
    @gBreq1d
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synCnc (.cv e))
      (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synCnc (.cv d)) (synClec) p0003
  have p0008 :=
    @gOrbi12d
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
      (synWbr (synCnc (.cv d)) (synClec)
        (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc))))
      (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d)))
      (synWbr (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
        (synClec) (synCnc (.cv d)))
      p0004 p0007
  have p0009 :=
    @gImbi2d
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
        (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))))
      (synWo (synWbr (synCnc (.cv d)) (synClec)
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
          (synClec) (synCnc (.cv d))))
      (synWbr (.cv r) (synCwe) (.cv d)) p0008
  have p0010 :=
    @gBiid
      (synWo (synWbr (synCnc (.cv d)) (synClec)
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
          (synClec) (synCnc (.cv d))))
  have p0011 :=
    @gA1i
      (synWb (synWo (synWbr (synCnc (.cv d)) (synClec)
            (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
            (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
            (synClec) (synCnc (.cv d)))) (synWo (synWbr (synCnc (.cv d)) (synClec)
            (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
            (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
            (synClec) (synCnc (.cv d)))))
      (.classEq (.cv r)
        (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin))))
      p0010
  have p0012 :=
    @gId
      (.classEq (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
  have p0013 :=
    @gNceqd
      (.classEq (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)) p0012
  have p0014 :=
    @gBreq1d
      (.classEq (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synCnc (.cv d))
      (synCnc (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synClec) p0013
  have p0017 :=
    @gBreq2d
      (.classEq (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synCnc (.cv d))
      (synCnc (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synClec) p0013
  have p0018 :=
    @gOrbi12d
      (.classEq (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synWbr (synCnc (.cv d)) (synClec)
        (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc))))
      (synWbr (synCnc (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
        (synClec) (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc))))
      (synWbr (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
        (synClec) (synCnc (.cv d)))
      (synWbr (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
        (synClec) (synCnc (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc))))
      p0014 p0017
  have p0019 :=
    @gId
      (.classEq (.cv r)
        (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin))))
  have p0020 :=
    @gBreq1d
      (.classEq (.cv r)
        (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin))))
      (.cv r)
      (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
      (.cv d) (synCwe) p0019
  have p0022 :=
    @gBreq2d
      (.classEq (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (.cv d) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc))
      (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
      (synCwe) p0012
  have p0023 :=
    @gId
      (.classEq (synCkqrel (synClefin))
        (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin))))
  have p0024 :=
    @gBreq1d
      (.classEq (synCkqrel (synClefin))
        (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin))))
      (synCkqrel (synClefin))
      (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
      (synCnnc) (synCwe) p0023
  have p0025 :=
    @gId
      (.classEq (synCnnc) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
  have p0026 :=
    @gBreq2d
      (.classEq (synCnnc) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synCnnc) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc))
      (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
      (synCwe) p0025
  have p0027 := @gFinlewe
  have p0028 :=
    @gElimhyp2v (synWbr (.cv r) (synCwe) (.cv d))
      (synWbr (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
        (synCwe) (.cv d))
      (synWbr (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
        (synCwe) (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))
      (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWbr (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
        (synCwe) (synCnnc))
      (.cv r) (.cv d) (synCkqrel (synClefin)) (synCnnc) p0020 p0022 p0024 p0026 p0027
  have p0029 :=
    @gId
      (.classEq (.cv s)
        (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin))))
  have p0030 :=
    @gBreq1d
      (.classEq (.cv s)
        (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin))))
      (.cv s)
      (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
      (.cv e) (synCwe) p0029
  have p0032 :=
    @gBreq2d
      (.classEq (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (.cv e) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc))
      (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
      (synCwe) p0002
  have p0033 :=
    @gId
      (.classEq (synCkqrel (synClefin))
        (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin))))
  have p0034 :=
    @gBreq1d
      (.classEq (synCkqrel (synClefin))
        (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin))))
      (synCkqrel (synClefin))
      (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
      (synCnnc) (synCwe) p0033
  have p0035 :=
    @gId
      (.classEq (synCnnc) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
  have p0036 :=
    @gBreq2d
      (.classEq (synCnnc) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synCnnc) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc))
      (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
      (synCwe) p0035
  have p0038 :=
    @gElimhyp2v (synWbr (.cv s) (synCwe) (.cv e))
      (synWbr (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
        (synCwe) (.cv e))
      (synWbr (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
        (synCwe) (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
      (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWbr (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
        (synCwe) (synCnnc))
      (.cv s) (.cv e) (synCkqrel (synClefin)) (synCnnc) p0030 p0032 p0034 p0036 p0027
  have p0039 :=
    @gWecomparisonnclecclndv
      (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc))
      (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv r) (synCkqrel (synClefin)))
      (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv s) (synCkqrel (synClefin)))
      (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)) p0028 p0038
  have p0040 :=
    @gDedth2v (synWbr (.cv r) (synCwe) (.cv d))
      (synWo (synWbr (synCnc (.cv d)) (synClec)
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
          (synClec) (synCnc (.cv d))))
      (synWo (synWbr (synCnc (.cv d)) (synClec)
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
          (synClec) (synCnc (.cv d))))
      (synWo (synWbr
          (synCnc (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc))) (synClec)
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
          (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc))) (synClec)
          (synCnc (synCif (synWbr (.cv r) (synCwe) (.cv d)) (.cv d) (synCnnc)))))
      (.cv r) (.cv d) (synCkqrel (synClefin)) (synCnnc) p0011 p0018 p0039
  have p0041 :=
    @gDedth2v (synWbr (.cv s) (synCwe) (.cv e))
      (.imp (synWbr (.cv r) (synCwe) (.cv d))
        (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
          (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d)))))
      (.imp (synWbr (.cv r) (synCwe) (.cv d))
        (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
          (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d)))))
      (.imp (synWbr (.cv r) (synCwe) (.cv d)) (synWo (synWbr (synCnc (.cv d)) (synClec)
            (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))) (synWbr
            (synCnc (synCif (synWbr (.cv s) (synCwe) (.cv e)) (.cv e) (synCnnc)))
            (synClec) (synCnc (.cv d)))))
      (.cv s) (.cv e) (synCkqrel (synClefin)) (synCnnc) p0001 p0009 p0040
  have p0042 :=
    @gImpcom (synWbr (.cv s) (synCwe) (.cv e)) (synWbr (.cv r) (synCwe) (.cv d))
      (synWo (synWbr (synCnc (.cv d)) (synClec) (synCnc (.cv e)))
        (synWbr (synCnc (.cv e)) (synClec) (synCnc (.cv d))))
      p0041
  exact p0042


end NFChoice.DirectNominalPrf.WPPReplay

end
