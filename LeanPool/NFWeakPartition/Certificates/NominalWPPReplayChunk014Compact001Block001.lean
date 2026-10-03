/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block014

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frecexg (F : Class) (G : Class) (I : Class) (V : Class)
    (hyp_frecex_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) :
    Nominal.NPrf (.imp (.classMem G V) (.classMem F (syn_cvv))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : x ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0002 : x ∉ (I).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_I, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G I
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqtri F (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      hyp_frecex_1 p0000
  have p0002 := @g_snex (syn_cop (syn_c0c) I)
  have p0003 := @g_csucex x
  have p0004 :=
    @g_pprodexg (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G (syn_cvv) V
  have p0005 :=
    @g_mpan (.classMem (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_cvv))
      (.classMem G V)
      (.classMem (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cvv))
      p0003 p0004
  have p0006 :=
    @g_clos1exg (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancr (.classMem G V) (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cvv))
      (.classMem (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_cvv))
      p0002 p0005 p0006
  have p0008 :=
    @g_syl5eqel (.classMem G V) F
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_cvv) p0001 p0007
  exact p0008

@[expose]
noncomputable def g_frecex (F : Class) (G : Class) (I : Class)
    (hyp_frecex_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_frecex_2 : Nominal.NPrf (.classMem G (syn_cvv))) :
    Nominal.NPrf (.classMem F (syn_cvv)) :=
  by
  have p0000 := @g_frecexg F G I (syn_cvv) hyp_frecex_1
  have p0001 := Nominal.mp hyp_frecex_2 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frecxp (F : Class) (G : Class) (I : Class)
    (hyp_frecxp_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_frecxp_2 : Nominal.NPrf (.classMem G (syn_cvv))) :
    Nominal.NPrf (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv
  let i : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  let c : Var := freshVar proofSupport 6
  let d : Var := freshVar proofSupport 7
  have fresh_i : i ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_i_not_G : i ∉ G.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_i_not_I : i ∉ I.fv := by
    intro h
    exact fresh_i (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_c_not_G : c ∉ G.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_i_ne_y : i ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_i : y ≠ i := Ne.symm fresh_i_ne_y
  have fresh_i_ne_z : i ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_i : z ≠ i := Ne.symm fresh_i_ne_z
  have fresh_i_ne_x : i ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_i : x ≠ i := Ne.symm fresh_i_ne_x
  have fresh_i_ne_a : i ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_i : a ≠ i := Ne.symm fresh_i_ne_a
  have fresh_i_ne_b : i ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_i : b ≠ i := Ne.symm fresh_i_ne_b
  have fresh_i_ne_c : i ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_c_ne_i : c ≠ i := Ne.symm fresh_i_ne_c
  have fresh_i_ne_d : i ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_d_ne_i : d ≠ i := Ne.symm fresh_i_ne_d
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_c : z ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_z_ne_d : z ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_d_ne_z : d ≠ z := Ne.symm fresh_z_ne_d
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have dv_cache_0001 : d ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_y, not_false_eq_true])
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
  have dv_cache_0003 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0004 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_z, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0008 : c ∉ ((Class.cv z)).fv :=
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
          fresh_c_ne_z, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0013 : d ∉ (G).fv :=
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
        simp only [fresh_d_not_G, not_false_eq_true])
  have dv_cache_0014 : a ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_G, not_false_eq_true])
  have dv_cache_0015 : b ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_G, not_false_eq_true])
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
  have dv_cache_0017 : d ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0018 : d ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show d ≠ b from (by exact fresh_d_ne_b))
  have dv_cache_0019 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0020 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0021 : a ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0022 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0023 : x ∉ ((Class.cv a)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_c, not_false_eq_true])
  have dv_cache_0025 :
    c ∉
      ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
          (.classMem (.cv z)
            (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_not_G, fresh_c_ne_i, fresh_c_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0026 :
    d ∉
      ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
          (.classMem (.cv z)
            (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_y, fresh_d_not_G, fresh_d_ne_i, fresh_d_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 :
    a ∉
      ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
          (.classMem (.cv z)
            (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_not_G, fresh_a_ne_i, fresh_a_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0028 :
    b ∉
      ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
          (.classMem (.cv z)
            (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_not_G, fresh_b_ne_i, fresh_b_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((Class.cv i)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_i, not_false_eq_true])
  have dv_cache_0031 : y ∉ ((syn_cfrec G (.cv i))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_G, fresh_y_ne_i, or_false, not_false_eq_true])
  have dv_cache_0032 : z ∉ ((syn_cfrec G (.cv i))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_G, fresh_z_ne_i, or_false, not_false_eq_true])
  have dv_cache_0033 :
    y ∉ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0034 :
    z ∉ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0035 :
    y ∉ ((syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_G, fresh_y_ne_i, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0036 :
    z ∉ ((syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_G, fresh_z_ne_i, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
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
  have dv_cache_0038 : i ∉ (I).fv :=
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
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_i_not_I, not_false_eq_true])
  have dv_cache_0039 :
    i ∉
      ((syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))).fv :=
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
        have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_i_not_G, fresh_i_not_I, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0040 : x ∉ (I).fv :=
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
        simp only [fresh_x_not_I, not_false_eq_true])
  have p0000 := @g_eqid G
  have p0001 := @g_freceq12 G G (.cv i) I
  have p0002 :=
    @g_mpan (.classEq G G) (.classEq (.cv i) I)
      (.classEq (syn_cfrec G (.cv i)) (syn_cfrec G I)) p0000 p0001
  have p0003 := @g_sneq (.cv i) I
  have p0004 :=
    @g_uneq2d (.classEq (.cv i) I) (syn_csn (.cv i)) (syn_csn I) (syn_crn G) p0003
  have p0005 :=
    @g_xpeq2d (.classEq (.cv i) I) (syn_cun (syn_crn G) (syn_csn (.cv i)))
      (syn_cun (syn_crn G) (syn_csn I)) (syn_cnnc) p0004
  have p0006 :=
    @g_sseq12d (.classEq (.cv i) I) (syn_cfrec G (.cv i)) (syn_cfrec G I)
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0002 p0005
  have p0007 := @g_nncex
  have p0008 := @g_rnex G hyp_frecxp_2
  have p0009 := @g_snex (.cv i)
  have p0010 := @g_unex (syn_crn G) (syn_csn (.cv i)) p0008 p0009
  have p0011 := @g_xpex (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))) p0007 p0010
  have p0012 := @g_peano1
  have p0013 := @g_vex i
  have p0014 := @g_snid (.cv i) p0013
  have p0015 := @g_elun2 (.cv i) (syn_csn (.cv i)) (syn_crn G)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_n_0cex
  have p0018 := @g_opex (syn_c0c) (.cv i) p0017 p0013
  have p0019 :=
    @g_snss (syn_cop (syn_c0c) (.cv i))
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0018
  have p0020 :=
    @g_opelxp (syn_c0c) (.cv i) (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))
  have p0021 :=
    @g_bitr3i
      (syn_wss (syn_csn (syn_cop (syn_c0c) (.cv i)))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (syn_cop (syn_c0c) (.cv i))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wa (.classMem (syn_c0c) (syn_cnnc))
        (.classMem (.cv i) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0019 p0020
  have p0022 :=
    @g_mpbir2an
      (syn_wss (syn_csn (syn_cop (syn_c0c) (.cv i)))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (syn_c0c) (syn_cnnc))
      (.classMem (.cv i) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0012 p0016 p0021
  have p0023 :=
    @g_brpprod a b c d (.cv y) (.cv z) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))
      G dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
  have p0024 := @g_vex a
  have p0025 := @g_vex c
  have p0026 := @g_brcsuc x (.cv a) (.cv c) dv_cache_0023 dv_cache_0024 p0024 p0025
  have p0027 := @g_brelrn (.cv b) (.cv d) G
  have p0028 := @g_elun1 (.cv d) (syn_crn G) (syn_csn (.cv i))
  have p0029 :=
    @g_syl (syn_wbr (.cv b) G (.cv d)) (.classMem (.cv d) (syn_crn G))
      (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0027 p0028
  have p0030 := @g_peano2 (.cv a)
  have p0031 :=
    @g_anim12ci (syn_wbr (.cv b) G (.cv d))
      (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))
      (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
      p0029 p0030
  have p0032 :=
    @g_adantrr (syn_wbr (.cv b) G (.cv d)) (.classMem (.cv a) (syn_cnnc))
      (syn_wa (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
        (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0031
  have p0033 := @g_eleq1 (.cv c) (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)
  have p0034 :=
    @g_anbi1d (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c)))
      (.classMem (.cv c) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
      (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0033
  have p0035 :=
    @g_syl5ibr
      (syn_wa (syn_wbr (.cv b) G (.cv d)) (syn_wa (.classMem (.cv a) (syn_cnnc))
          (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      (syn_wa (.classMem (.cv c) (syn_cnnc))
        (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c)))
      (syn_wa (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
        (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0032 p0034
  have p0036 :=
    @g_exp3a (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c))) (syn_wbr (.cv b) G (.cv d))
      (syn_wa (.classMem (.cv a) (syn_cnnc))
        (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wa (.classMem (.cv c) (syn_cnnc))
        (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0035
  have p0037 :=
    @g_sylbi (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
      (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c)))
      (.imp (syn_wbr (.cv b) G (.cv d)) (.imp (syn_wa (.classMem (.cv a) (syn_cnnc))
            (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
          (syn_wa (.classMem (.cv c) (syn_cnnc))
            (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))))
      p0026 p0036
  have p0038 :=
    @g_imp (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
      (syn_wbr (.cv b) G (.cv d))
      (.imp (syn_wa (.classMem (.cv a) (syn_cnnc))
          (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (syn_wa (.classMem (.cv c) (syn_cnnc))
          (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      p0037
  have p0039 :=
    @g_eleq1 (.cv y) (syn_cop (.cv a) (.cv b))
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))
  have p0040 :=
    @g_opelxp (.cv a) (.cv b) (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))
  have p0041 :=
    @g_syl6bb (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
      (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (syn_cop (.cv a) (.cv b))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wa (.classMem (.cv a) (syn_cnnc))
        (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0039 p0040
  have p0042 :=
    @g_adantr (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
      (syn_wb (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (syn_wa (.classMem (.cv a) (syn_cnnc))
          (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) p0041
  have p0043 :=
    @g_eleq1 (.cv z) (syn_cop (.cv c) (.cv d))
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))
  have p0044 :=
    @g_opelxp (.cv c) (.cv d) (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))
  have p0045 :=
    @g_syl6bb (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
      (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (syn_cop (.cv c) (.cv d))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wa (.classMem (.cv c) (syn_cnnc))
        (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0043 p0044
  have p0046 :=
    @g_adantl (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
      (syn_wb (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (syn_wa (.classMem (.cv c) (syn_cnnc))
          (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) p0045
  have p0047 :=
    @g_imbi12d
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wa (.classMem (.cv a) (syn_cnnc))
        (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wa (.classMem (.cv c) (syn_cnnc))
        (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0042 p0046
  have p0048 :=
    @g_syl5ibr
      (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
        (syn_wbr (.cv b) G (.cv d)))
      (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))))
      (.imp (syn_wa (.classMem (.cv a) (syn_cnnc))
          (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (syn_wa (.classMem (.cv c) (syn_cnnc))
          (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      p0038 p0047
  have p0049 :=
    @g_n_3impia (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
      (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))
      (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
        (syn_wbr (.cv b) G (.cv d)))
      (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      p0048
  have p0050 :=
    @g_exlimivv
      (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa
          (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
          (syn_wbr (.cv b) G (.cv d))))
      (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      c d dv_cache_0025 dv_cache_0026 p0049
  have p0051 :=
    @g_exlimivv
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
            (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa
              (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
              (syn_wbr (.cv b) G (.cv d))))))
      (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      a b dv_cache_0027 dv_cache_0028 p0050
  have p0052 :=
    @g_sylbi
      (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
        (.cv z))
      (syn_wex a (syn_wex b (syn_wex c (syn_wex d
              (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b)))
                (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa
                  (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c))
                  (syn_wbr (.cv b) G (.cv d))))))))
      (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
        (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))
      p0023 p0051
  have p0053 :=
    @g_impcom
      (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
        (.cv z))
      (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0052
  have p0054 := Nominal.gen p0053 z
  have p0055 :=
    @g_rgenw
      (.all z (.imp (syn_wa (.classMem (.cv y)
              (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wbr (.cv y)
              (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (.cv z)))
          (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))))
      y (syn_cfrec G (.cv i)) p0054
  have p0056 := @g_snex (syn_cop (syn_c0c) (.cv i))
  have p0057 := @g_csucex x
  have p0058 :=
    @g_pprodex (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G p0057 hyp_frecxp_2
  have p0059 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G (.cv i)
      dv_cache_0029 dv_cache_0030
  have p0060 :=
    @g_clos1induct y z (syn_cfrec G (.cv i))
      (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) (.cv i))) (syn_cvv)
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) dv_cache_0031
      dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
      p0056 p0058 p0059
  have p0061 :=
    @g_mp3an
      (.classMem (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) (syn_cvv))
      (syn_wss (syn_csn (syn_cop (syn_c0c) (.cv i)))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wral y (syn_cfrec G (.cv i)) (.all z (.imp (syn_wa (.classMem (.cv y)
                (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wbr (.cv y)
                (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (.cv z)))
            (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))))
      (syn_wss (syn_cfrec G (.cv i))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      p0011 p0022 p0055 p0060
  have p0062 :=
    @g_vtoclg
      (syn_wss (syn_cfrec G (.cv i))
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))
      (syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) i I
      (syn_cvv) dv_cache_0038 dv_cache_0039 p0006 p0061
  have p0063 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G I
      dv_cache_0029 dv_cache_0040
  have p0064 := @g_opexb (syn_c0c) I
  have p0065 :=
    @g_simprbi (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (.classMem (syn_c0c) (syn_cvv))
      (.classMem I (syn_cvv)) p0064
  have p0066 :=
    @g_con3i (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (.classMem I (syn_cvv)) p0065
  have p0067 := @g_snprc (syn_cop (syn_c0c) I)
  have p0068 :=
    @g_sylib (.neg (.classMem I (syn_cvv)))
      (.neg (.classMem (syn_cop (syn_c0c) I) (syn_cvv)))
      (.classEq (syn_csn (syn_cop (syn_c0c) I)) (syn_c0)) p0066 p0067
  have p0069 :=
    @g_clos1eq1 (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_c0)
  have p0070 :=
    @g_syl (.neg (.classMem I (syn_cvv)))
      (.classEq (syn_csn (syn_cop (syn_c0c) I)) (syn_c0))
      (.classEq (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
        (syn_cclos1 (syn_c0)
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)))
      p0068 p0069
  have p0071 :=
    @g_eqid
      (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
  have p0072 :=
    @g_clos10
      (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) p0058 p0071
  have p0073 :=
    @g_syl6eq (.neg (.classMem I (syn_cvv)))
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_c0) p0070 p0072
  have p0074 := @g_n_0ss (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
  have p0075 :=
    @g_syl6eqss (.neg (.classMem I (syn_cvv)))
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_c0) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0073 p0074
  have p0076 :=
    @g_syl5eqss (.neg (.classMem I (syn_cvv))) (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0063 p0075
  have p0077 :=
    @g_pm2_61i (.classMem I (syn_cvv))
      (syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))
      p0062 p0076
  have p0078 :=
    @g_eqsstri F (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
      hyp_frecxp_1 p0077
  exact p0078


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frecxpg (F : Class) (G : Class) (I : Class) (V : Class)
    (hyp_frecxpg_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) :
    Nominal.NPrf
      (.imp (.classMem G V)
        (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv ∪ V.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_G : g ∉ G.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_I : g ∉ I.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : g ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_G, not_false_eq_true])
  have dv_cache_0002 :
    g ∉
      ((syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_g_not_G, fresh_g_not_I, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_eqid I
  have p0001 := @g_freceq12 (.cv g) G I I
  have p0002 :=
    @g_mpan2 (.classEq (.cv g) G) (.classEq I I)
      (.classEq (syn_cfrec (.cv g) I) (syn_cfrec G I)) p0000 p0001
  have p0003 := @g_rneq (.cv g) G
  have p0004 :=
    @g_uneq1d (.classEq (.cv g) G) (syn_crn (.cv g)) (syn_crn G) (syn_csn I) p0003
  have p0005 :=
    @g_xpeq2d (.classEq (.cv g) G) (syn_cun (syn_crn (.cv g)) (syn_csn I))
      (syn_cun (syn_crn G) (syn_csn I)) (syn_cnnc) p0004
  have p0006 :=
    @g_sseq12d (.classEq (.cv g) G) (syn_cfrec (.cv g) I) (syn_cfrec G I)
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn (.cv g)) (syn_csn I)))
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0002 p0005
  have p0007 := @g_eqid (syn_cfrec (.cv g) I)
  have p0008 := @g_vex g
  have p0009 := @g_frecxp (syn_cfrec (.cv g) I) (.cv g) I p0007 p0008
  have p0010 :=
    @g_vtoclg
      (syn_wss (syn_cfrec (.cv g) I)
        (syn_cxp (syn_cnnc) (syn_cun (syn_crn (.cv g)) (syn_csn I))))
      (syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) g G
      V dv_cache_0001 dv_cache_0002 p0006 p0009
  have p0011 :=
    @g_syl5eqss (.classMem G V) F (syn_cfrec G I)
      (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) hyp_frecxpg_1 p0010
  exact p0011

@[expose]
noncomputable def g_dmfrec (ph : Wff) (F : Class) (G : Class) (I : Class) (V : Class)
    (hyp_dmfrec_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_dmfrec_2 : Nominal.NPrf (.imp ph (.classMem G V)))
    (hyp_dmfrec_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G))))
    (hyp_dmfrec_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdm F) (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_G : t ∉ G.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_I : t ∉ I.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : w ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_G, not_false_eq_true])
  have dv_cache_0002 : w ∉ (I).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_I, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_cop (syn_c0c) I)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_t_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_F, not_false_eq_true])
  have dv_cache_0005 :
    t ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_w, fresh_t_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_t_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
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
  have dv_cache_0008 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((syn_cop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Wff.classMem (.cv y) (syn_cdm G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_not_G, or_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_ph, not_false_eq_true])
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
  have dv_cache_0013 : z ∉ (G).fv :=
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
        simp only [fresh_z_not_G, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Class.cv x)).fv :=
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
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((syn_cplc (.cv x) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (syn_cop (.cv x) (.cv y)) F)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cplc (.cv x) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0018 : z ∉ (F).fv :=
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
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Wff.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (ph).fv :=
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
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0021 : x ∉ (ph).fv :=
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
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((syn_cdm F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_F,
          not_false_eq_true])
  have p0000 := @g_frecxpg F G I V hyp_dmfrec_1
  have p0001 := @g_dmss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
  have p0002 :=
    @g_n_3syl ph (.classMem G V)
      (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))
      (syn_wss (syn_cdm F) (syn_cdm (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))))
      hyp_dmfrec_2 p0000 p0001
  have p0003 := @g_dmxpss (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))
  have p0004 :=
    @g_syl6ss ph (syn_cdm F)
      (syn_cdm (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) (syn_cnnc) p0002
      p0003
  have p0005 := @g_frecexg F G I V hyp_dmfrec_1
  have p0006 := @g_syl ph (.classMem G V) (.classMem F (syn_cvv)) hyp_dmfrec_2 p0005
  have p0007 := @g_dmexg F (syn_cvv)
  have p0008 :=
    @g_syl ph (.classMem F (syn_cvv)) (.classMem (syn_cdm F) (syn_cvv)) p0006 p0007
  have p0009 := @g_n_0cex
  have p0010 := @g_opexg (syn_c0c) I (syn_cvv) (syn_cdm G)
  have p0011 :=
    @g_mpan (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cdm G))
      (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_syl ph (.classMem I (syn_cdm G)) (.classMem (syn_cop (syn_c0c) I) (syn_cvv))
      hyp_dmfrec_3 p0011
  have p0013 := @g_snidg (syn_cop (syn_c0c) I) (syn_cvv)
  have p0014 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv))
      (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) p0012 p0013
  have p0015 :=
    @g_orcd ph (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I)))
      (syn_wrex t F (syn_wbr (.cv t)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_c0c) I)))
      p0014
  have p0016 := @g_snex (syn_cop (syn_c0c) I)
  have p0017 := @g_csucex w
  have p0018 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) V
  have p0019 :=
    @g_mpan (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv))
      (.classMem G V)
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      p0017 p0018
  have p0020 :=
    @g_syl ph (.classMem G V)
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      hyp_dmfrec_2 p0019
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I
      dv_cache_0001 dv_cache_0002
  have p0022 :=
    @g_eqtri F (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G))
      hyp_dmfrec_1 p0021
  have p0023 :=
    @g_clos1basesucg t (syn_cop (syn_c0c) I) F
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0022
  have p0024 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_c0c) I) F)
        (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F
            (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
              (syn_cop (syn_c0c) I)))))
      p0016 p0020 p0023
  have p0025 :=
    @g_mpbird ph (.classMem (syn_cop (syn_c0c) I) F)
      (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex t F
          (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_c0c) I))))
      p0015 p0024
  have p0026 := @g_opeldm (syn_c0c) I F
  have p0027 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) F) (.classMem (syn_c0c) (syn_cdm F)) p0025
      p0026
  have p0028 := @g_eldm2 y (.cv x) F dv_cache_0007 dv_cache_0008
  have p0029 :=
    @g_clos1basesucg t (syn_cop (.cv x) (.cv y)) F
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0009 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0022
  have p0030 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F)
        (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I)))
          (syn_wrex t F (syn_wbr (.cv t)
              (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
              (syn_cop (.cv x) (.cv y))))))
      p0016 p0020 p0029
  have p0031 := @g_vex x
  have p0032 := @g_vex y
  have p0033 := @g_opex (.cv x) (.cv y) p0031 p0032
  have p0034 := @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop (syn_c0c) I) p0033
  have p0035 := @g_opth (.cv x) (.cv y) (syn_c0c) I
  have p0036 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (syn_c0c) I))
      (syn_wa (.classEq (.cv x) (syn_c0c)) (.classEq (.cv y) I)) p0034 p0035
  have p0037 :=
    @g_simprbi (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I)))
      (.classEq (.cv x) (syn_c0c)) (.classEq (.cv y) I) p0036
  have p0038 := @g_eleq1 (.cv y) I (syn_cdm G)
  have p0039 :=
    @g_biimprcd (.classEq (.cv y) I) (.classMem (.cv y) (syn_cdm G))
      (.classMem I (syn_cdm G)) p0038
  have p0040 :=
    @g_syl ph (.classMem I (syn_cdm G))
      (.imp (.classEq (.cv y) I) (.classMem (.cv y) (syn_cdm G))) hyp_dmfrec_3 p0039
  have p0041 :=
    @g_syl5 (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I)))
      (.classEq (.cv y) I) ph (.classMem (.cv y) (syn_cdm G)) p0037 p0040
  have p0042 := @g_opeq (.cv t)
  have p0043 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)))
      (syn_cop (.cv x) (.cv y))
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) p0042
  have p0044 :=
    @g_qrpprod (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (.cv x) (.cv y)
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0045 :=
    @g_bitri
      (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (.cv x) (.cv y)))
      (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (.cv x) (.cv y)))
      (syn_wa (syn_wbr (syn_cproj1 (.cv t)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (.cv x)) (syn_wbr (syn_cproj2 (.cv t)) G (.cv y)))
      p0043 p0044
  have p0046 :=
    @g_simprbi
      (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (.cv x) (.cv y)))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv x))
      (syn_wbr (syn_cproj2 (.cv t)) G (.cv y)) p0045
  have p0047 := @g_brelrn (syn_cproj2 (.cv t)) (.cv y) G
  have p0048 :=
    @g_syl
      (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (.cv x) (.cv y)))
      (syn_wbr (syn_cproj2 (.cv t)) G (.cv y)) (.classMem (.cv y) (syn_crn G)) p0046 p0047
  have p0049 := @g_sseld ph (syn_crn G) (syn_cdm G) (.cv y) hyp_dmfrec_4
  have p0050 :=
    @g_syl5
      (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (.cv x) (.cv y)))
      (.classMem (.cv y) (syn_crn G)) ph (.classMem (.cv y) (syn_cdm G)) p0048 p0049
  have p0051 :=
    @g_adantr ph
      (.imp (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (.cv x) (.cv y))) (.classMem (.cv y) (syn_cdm G)))
      (.classMem (.cv t) F) p0050
  have p0052 :=
    @g_rexlimdva ph
      (syn_wbr (.cv t) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (.cv x) (.cv y)))
      (.classMem (.cv y) (syn_cdm G)) t F dv_cache_0010 dv_cache_0011 p0051
  have p0053 :=
    @g_jaod ph (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I)))
      (.classMem (.cv y) (syn_cdm G))
      (syn_wrex t F (syn_wbr (.cv t)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (.cv x) (.cv y))))
      p0041 p0052
  have p0054 :=
    @g_sylbid ph (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop (syn_c0c) I)))
        (syn_wrex t F (syn_wbr (.cv t)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (.cv x) (.cv y)))))
      (.classMem (.cv y) (syn_cdm G)) p0030 p0053
  have p0055 :=
    @g_ancld ph (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G))
      p0054
  have p0056 :=
    @g_clos1conn (syn_cop (.cv x) (.cv y)) (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))
      F (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) p0022
  have p0057 :=
    @g_eximi
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wbr (syn_cop (.cv x) (.cv y))
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))))
      (.classMem (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)) F) z p0056
  have p0058 := @g_eldm z (.cv y) G dv_cache_0012 dv_cache_0013
  have p0059 := @g_eqid (syn_cplc (.cv x) (syn_c1c))
  have p0060 := @g_n_1cex
  have p0061 := @g_addcex (.cv x) (syn_c1c) p0031 p0060
  have p0062 :=
    @g_brcsuc w (.cv x) (syn_cplc (.cv x) (syn_c1c)) dv_cache_0014 dv_cache_0015 p0031
      p0061
  have p0063 :=
    @g_mpbir
      (syn_wbr (.cv x) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
        (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))) p0059 p0062
  have p0064 :=
    @g_qrpprod (.cv x) (.cv y) (syn_cplc (.cv x) (syn_c1c)) (.cv z)
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0065 :=
    @g_mpbiran
      (syn_wbr (syn_cop (.cv x) (.cv y))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))
      (syn_wbr (.cv x) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
        (syn_cplc (.cv x) (syn_c1c)))
      (syn_wbr (.cv y) G (.cv z)) p0063 p0064
  have p0066 :=
    @g_exbii
      (syn_wbr (syn_cop (.cv x) (.cv y))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))
      (syn_wbr (.cv y) G (.cv z)) z p0065
  have p0067 :=
    @g_bitr4i (.classMem (.cv y) (syn_cdm G)) (syn_wex z (syn_wbr (.cv y) G (.cv z)))
      (syn_wex z (syn_wbr (syn_cop (.cv x) (.cv y))
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))))
      p0058 p0066
  have p0068 :=
    @g_anbi2i (.classMem (.cv y) (syn_cdm G))
      (syn_wex z (syn_wbr (syn_cop (.cv x) (.cv y))
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z))))
      (.classMem (syn_cop (.cv x) (.cv y)) F) p0067
  have p0069 :=
    @g_n_19_42v (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wbr (syn_cop (.cv x) (.cv y))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))
      z dv_cache_0016
  have p0070 :=
    @g_bitr4i
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wex z
          (syn_wbr (syn_cop (.cv x) (.cv y))
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))))
      (syn_wex z (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (syn_wbr (syn_cop (.cv x) (.cv y))
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))))
      p0068 p0069
  have p0071 := @g_eldm2 z (syn_cplc (.cv x) (syn_c1c)) F dv_cache_0017 dv_cache_0018
  have p0072 :=
    @g_n_3imtr4i
      (syn_wex z (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (syn_wbr (syn_cop (.cv x) (.cv y))
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)))))
      (syn_wex z (.classMem (syn_cop (syn_cplc (.cv x) (syn_c1c)) (.cv z)) F))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G)))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) p0057 p0070 p0071
  have p0073 :=
    @g_syl6 ph (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv y) (syn_cdm G)))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) p0055 p0072
  have p0074 :=
    @g_exlimdv ph (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) y dv_cache_0019 dv_cache_0020
      p0073
  have p0075 :=
    @g_syl5bi (.classMem (.cv x) (syn_cdm F))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) F)) ph
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)) p0028 p0074
  have p0076 :=
    @g_ralrimivw ph
      (.imp (.classMem (.cv x) (syn_cdm F))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F)))
      x (syn_cnnc) dv_cache_0021 p0075
  have p0077 := @g_peano5 x (syn_cdm F) (syn_cvv) dv_cache_0022
  have p0078 :=
    @g_syl3anc ph (.classMem (syn_cdm F) (syn_cvv)) (.classMem (syn_c0c) (syn_cdm F))
      (syn_wral x (syn_cnnc) (.imp (.classMem (.cv x) (syn_cdm F))
          (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cdm F))))
      (syn_wss (syn_cnnc) (syn_cdm F)) p0008 p0027 p0076 p0077
  have p0079 := @g_eqssd ph (syn_cdm F) (syn_cnnc) p0004 p0078
  exact p0079

@[expose]
noncomputable def g_fnfreclem1 (y : Var) (z : Var) (w : Var) (F : Class) (V : Class)
    (dv_F_w : w ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_w_y : w ≠ y)
    (dv_w_z : w ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.classMem F V) (.classMem (.cab w (.all y (.all z
                (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
                  (.objEq y z))))) (syn_cvv))) :=
  by
  have dv_cache_0001 : y ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_w_y), not_false_eq_true])
  have dv_cache_0002 :
    y ∉
      ((syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, dv_F_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (.cv y) (.cv w))).fv :=
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
          Finset.mem_singleton, (Ne.symm dv_y_z), (Ne.symm dv_w_z), or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, dv_F_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    w ∉
      ((syn_ccompl (syn_crn (syn_crn (syn_cdif
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
                (syn_cins3 (syn_cid))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, dv_F_w,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_vex w
  have p0001 :=
    @g_elcompl (.cv w)
      (syn_crn (syn_crn
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))))
      p0000
  have p0002 :=
    @g_elrn2 y (.cv w)
      (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid))))
      dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_elrn2 z (syn_cop (.cv y) (.cv w))
      (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
        (syn_cins3 (syn_cid)))
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_eldif (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
      (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
      (syn_cins3 (syn_cid))
  have p0005 :=
    @g_elin (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F))
      (syn_cins2 (syn_ccnv F))
  have p0006 := @g_opelcnv (.cv y) (.cv w) F
  have p0007 := @g_vex z
  have p0008 := @g_opelxp (.cv z) (syn_cop (.cv y) (.cv w)) (syn_cvv) (syn_ccnv F)
  have p0009 :=
    @g_mpbiran
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F)))
      (.classMem (.cv z) (syn_cvv)) (.classMem (syn_cop (.cv y) (.cv w)) (syn_ccnv F))
      p0007 p0008
  have p0010 := (Nominal.biimpRefl (syn_wbr (.cv w) F (.cv y)))
  have p0011 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv y) (.cv w)) (syn_ccnv F))
      (.classMem (syn_cop (.cv w) (.cv y)) F)
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F)))
      (syn_wbr (.cv w) F (.cv y)) p0006 p0009 p0010
  have p0012 := @g_opelcnv (.cv z) (.cv w) F
  have p0013 := @g_vex y
  have p0014 := @g_otelins2 (.cv z) (.cv y) (.cv w) (syn_ccnv F) p0013
  have p0015 := (Nominal.biimpRefl (syn_wbr (.cv w) F (.cv z)))
  have p0016 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv z) (.cv w)) (syn_ccnv F))
      (.classMem (syn_cop (.cv w) (.cv z)) F)
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins2 (syn_ccnv F)))
      (syn_wbr (.cv w) F (.cv z)) p0012 p0014 p0015
  have p0017 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cxp (syn_cvv) (syn_ccnv F)))
      (syn_wbr (.cv w) F (.cv y))
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins2 (syn_ccnv F)))
      (syn_wbr (.cv w) F (.cv z)) p0011 p0016
  have p0018 :=
    @g_bitri
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
        (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))))
      (syn_wa (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
          (syn_cxp (syn_cvv) (syn_ccnv F)))
        (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins2 (syn_ccnv F))))
      (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) p0005 p0017
  have p0019 := @g_otelins3 (.cv z) (.cv y) (.cv w) (syn_cid) p0000
  have p0020 := (Nominal.biimpRefl (syn_wbr (.cv z) (syn_cid) (.cv y)))
  have p0021 := @g_ideq (.cv z) (.cv y) p0013
  have p0022 := @g_equcom z y
  have p0023_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv z) (syn_cid) (.cv y)) (.objEq z y)) :=
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
      p0021
  have p0023 :=
    @g_bitri (syn_wbr (.cv z) (syn_cid) (.cv y)) (.objEq z y) (.objEq y z)
      p0023_e00_recanon p0022
  have p0024 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid)))
      (.classMem (syn_cop (.cv z) (.cv y)) (syn_cid)) (syn_wbr (.cv z) (syn_cid) (.cv y))
      (.objEq y z) p0019 p0020 p0023
  have p0025 :=
    @g_notbii
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid)))
      (.objEq y z) p0024
  have p0026 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
        (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))))
      (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
      (.neg (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid))))
      (.neg (.objEq y z)) p0018 p0025
  have p0027 :=
    @g_bitri
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
        (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid))))
      (syn_wa (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
          (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))) (.neg
          (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w))) (syn_cins3 (syn_cid)))))
      (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
        (.neg (.objEq y z)))
      p0004 p0026
  have p0028 :=
    @g_exbii
      (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
        (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid))))
      (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
        (.neg (.objEq y z)))
      z p0027
  have p0029 :=
    @g_bitri
      (.classMem (syn_cop (.cv y) (.cv w)) (syn_crn
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))))
      (syn_wex z (.classMem (syn_cop (.cv z) (syn_cop (.cv y) (.cv w)))
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))))
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
          (.neg (.objEq y z))))
      p0003 p0028
  have p0030 :=
    @g_exbii
      (.classMem (syn_cop (.cv y) (.cv w)) (syn_crn
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))))
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
          (.neg (.objEq y z))))
      y p0029
  have p0031 :=
    @g_exanali (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
      (.objEq y z) z
  have p0032 :=
    @g_exbii
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
          (.neg (.objEq y z))))
      (.neg (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.objEq y z))))
      y p0031
  have p0033 :=
    @g_exnal
      (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
          (.objEq y z)))
      y
  have p0034 :=
    @g_bitri
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.neg (.objEq y z)))))
      (syn_wex y (.neg (.all z
            (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      (.neg (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      p0032 p0033
  have p0035 :=
    @g_n_3bitrri
      (.classMem (.cv w) (syn_crn (syn_crn
            (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
              (syn_cins3 (syn_cid))))))
      (syn_wex y (.classMem (syn_cop (.cv y) (.cv w)) (syn_crn
            (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
              (syn_cins3 (syn_cid))))))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.neg (.objEq y z)))))
      (.neg (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      p0002 p0030 p0034
  have p0036 :=
    @g_con1bii
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.objEq y z))))
      (.classMem (.cv w) (syn_crn (syn_crn
            (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
              (syn_cins3 (syn_cid))))))
      p0035
  have p0037 :=
    @g_bitri
      (.classMem (.cv w) (syn_ccompl (syn_crn (syn_crn (syn_cdif
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
                (syn_cins3 (syn_cid)))))))
      (.neg (.classMem (.cv w) (syn_crn (syn_crn (syn_cdif
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
                (syn_cins3 (syn_cid)))))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.objEq y z))))
      p0001 p0036
  have p0038 :=
    @g_eqabi
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.objEq y z))))
      w
      (syn_ccompl (syn_crn (syn_crn
            (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
              (syn_cins3 (syn_cid))))))
      dv_cache_0005 p0037
  have p0039 := @g_vvex
  have p0040 := @g_cnvexg F V
  have p0041 := @g_xpexg (syn_cvv) (syn_ccnv F) (syn_cvv) (syn_cvv)
  have p0042 :=
    @g_sylancr (.classMem F V) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_ccnv F) (syn_cvv))
      (.classMem (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cvv)) p0039 p0040 p0041
  have p0043 := @g_ins2exg (syn_ccnv F) (syn_cvv)
  have p0044 :=
    @g_syl (.classMem F V) (.classMem (syn_ccnv F) (syn_cvv))
      (.classMem (syn_cins2 (syn_ccnv F)) (syn_cvv)) p0040 p0043
  have p0045 :=
    @g_inexg (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)) (syn_cvv) (syn_cvv)
  have p0046 :=
    @g_syl2anc (.classMem F V) (.classMem (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cvv))
      (.classMem (syn_cins2 (syn_ccnv F)) (syn_cvv))
      (.classMem (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cvv))
      p0042 p0044 p0045
  have p0047 := @g_idex
  have p0048 := @g_ins3ex (syn_cid) p0047
  have p0049 :=
    @g_difexg (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
      (syn_cins3 (syn_cid)) (syn_cvv) (syn_cvv)
  have p0050 :=
    @g_mpan2
      (.classMem (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cvv))
      (.classMem (syn_cins3 (syn_cid)) (syn_cvv))
      (.classMem (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid))) (syn_cvv))
      p0048 p0049
  have p0051 :=
    @g_rnexg
      (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
        (syn_cins3 (syn_cid)))
      (syn_cvv)
  have p0052 :=
    @g_n_3syl (.classMem F V)
      (.classMem (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F))) (syn_cvv))
      (.classMem (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid))) (syn_cvv))
      (.classMem (syn_crn
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))) (syn_cvv))
      p0046 p0050 p0051
  have p0053 :=
    @g_rnexg
      (syn_crn (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
          (syn_cins3 (syn_cid))))
      (syn_cvv)
  have p0054 :=
    @g_complexg
      (syn_crn (syn_crn
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))))
      (syn_cvv)
  have p0055 :=
    @g_n_3syl (.classMem F V)
      (.classMem (syn_crn
          (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
            (syn_cins3 (syn_cid)))) (syn_cvv))
      (.classMem (syn_crn (syn_crn
            (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
              (syn_cins3 (syn_cid))))) (syn_cvv))
      (.classMem (syn_ccompl (syn_crn (syn_crn (syn_cdif
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
                (syn_cins3 (syn_cid)))))) (syn_cvv))
      p0052 p0053 p0054
  have p0056 :=
    @g_syl5eqelr (.classMem F V)
      (.cab w (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      (syn_ccompl (syn_crn (syn_crn
            (syn_cdif (syn_cin (syn_cxp (syn_cvv) (syn_ccnv F)) (syn_cins2 (syn_ccnv F)))
              (syn_cins3 (syn_cid))))))
      (syn_cvv) p0038 p0055
  exact p0056


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fnfreclem2 (ph : Wff) (F : Class) (G : Class) (I : Class) (V : Class)
    (X : Class) (hyp_fnfreclem2_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_fnfreclem2_2 : Nominal.NPrf (.imp ph (.classMem G V)))
    (hyp_fnfreclem2_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G))))
    (_hyp_fnfreclem2_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wbr (syn_c0c) F X) (.classEq X I))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv ∪ V.fv ∪ X.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_G, not_false_eq_true])
  have dv_cache_0002 : w ∉ (I).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_I, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (syn_c0c) X)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_z_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0005 :
    z ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_z_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((syn_cproj1 (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_z,
          not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_cplc (syn_cproj1 (.cv z)) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (syn_wbr (syn_c0c) F X))
  have p0001 := @g_snex (syn_cop (syn_c0c) I)
  have p0002 := @g_csucex w
  have p0003 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) V
  have p0004 :=
    @g_sylancr ph
      (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv))
      (.classMem G V)
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      p0002 hyp_fnfreclem2_2 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I
      dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_eqtri F (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G))
      hyp_fnfreclem2_1 p0005
  have p0007 :=
    @g_clos1basesucg z (syn_cop (syn_c0c) X) F
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_c0c) X) F)
        (syn_wo (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex z F
            (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
              (syn_cop (syn_c0c) X)))))
      p0001 p0004 p0007
  have p0009 := @g_n_0cex
  have p0010 := @g_opexg (syn_c0c) I (syn_cvv) (syn_cdm G)
  have p0011 :=
    @g_sylancr ph (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cdm G))
      (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0009 hyp_fnfreclem2_3 p0010
  have p0012 := @g_elsnc2g (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I) (syn_cvv)
  have p0013 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I)))
        (.classEq (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I)))
      p0011 p0012
  have p0014 := @g_opth (syn_c0c) X (syn_c0c) I
  have p0015 :=
    @g_simprbi (.classEq (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I))
      (.classEq (syn_c0c) (syn_c0c)) (.classEq X I) p0014
  have p0016 :=
    @g_syl6bi ph (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I)))
      (.classEq (syn_cop (syn_c0c) X) (syn_cop (syn_c0c) I)) (.classEq X I) p0013 p0015
  have p0017 := @g_n_0cnsuc (syn_cproj1 (.cv z))
  have p0018 :=
    (Nominal.biimpRefl (syn_wne (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c)))
  have p0019 :=
    @g_mpbi (syn_wne (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))
      (.neg (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))) p0017 p0018
  have p0020 :=
    @g_intnanr (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))
      (syn_wbr (syn_cproj2 (.cv z)) G X) p0019
  have p0021 :=
    @g_qrpprod (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)) (syn_c0c) X
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0022 := @g_opeq (.cv z)
  have p0023 :=
    @g_breq1i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)))
      (syn_cop (syn_c0c) X)
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) p0022
  have p0024 := @g_vex z
  have p0025 := @g_proj1ex (.cv z) p0024
  have p0026 := @g_addceq1 (.cv w) (syn_cproj1 (.cv z)) (syn_c1c)
  have p0027 := @g_eqid (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0028 := @g_n_1cex
  have p0029 := @g_addcex (syn_cproj1 (.cv z)) (syn_c1c) p0025 p0028
  have p0030 :=
    @g_fvmpt w (syn_cproj1 (.cv z)) (syn_cplc (.cv w) (syn_c1c))
      (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_cvv)
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0026 p0027 p0029
  have p0031 := Nominal.mp p0025 p0030
  have p0032 :=
    @g_eqeq1i
      (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cproj1 (.cv z)))
      (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c) p0031
  have p0033 := @g_vex w
  have p0035 := @g_addcex (.cv w) (syn_c1c) p0033 p0028
  have p0036 :=
    @g_fnmpti w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0009 p0035 p0027
  have p0037 :=
    @g_fnbrfvb (syn_cvv) (syn_cproj1 (.cv z)) (syn_c0c)
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0038 :=
    @g_mp2an (syn_wfn (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv))
      (.classMem (syn_cproj1 (.cv z)) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
            (syn_cproj1 (.cv z))) (syn_c0c))
        (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_c0c)))
      p0036 p0025 p0037
  have p0039 :=
    @g_bitr3i (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))
      (.classEq
        (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cproj1 (.cv z)))
        (syn_c0c))
      (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
        (syn_c0c))
      p0032 p0038
  have p0040 :=
    @g_anbi1i (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))
      (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
        (syn_c0c))
      (syn_wbr (syn_cproj2 (.cv z)) G X) p0039
  have p0041 :=
    @g_n_3bitr4i
      (syn_wbr (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_c0c) X))
      (syn_wa (syn_wbr (syn_cproj1 (.cv z)) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_c0c)) (syn_wbr (syn_cproj2 (.cv z)) G X))
      (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_c0c) X))
      (syn_wa (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))
        (syn_wbr (syn_cproj2 (.cv z)) G X))
      p0021 p0023 p0040
  have p0042 :=
    @g_mtbir
      (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_c0c) X))
      (syn_wa (.classEq (syn_cplc (syn_cproj1 (.cv z)) (syn_c1c)) (syn_c0c))
        (syn_wbr (syn_cproj2 (.cv z)) G X))
      p0020 p0041
  have p0043 :=
    @g_a1i
      (.neg (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_c0c) X)))
      (.classMem (.cv z) F) p0042
  have p0044 :=
    @g_nrex
      (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_c0c) X))
      z F p0043
  have p0045 :=
    @g_pm2_21i
      (syn_wrex z F (syn_wbr (.cv z)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_c0c) X)))
      (.classEq X I) p0044
  have p0046 :=
    @g_a1i
      (.imp (syn_wrex z F (syn_wbr (.cv z)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_c0c) X))) (.classEq X I))
      ph p0045
  have p0047 :=
    @g_jaod ph (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I)))
      (.classEq X I)
      (syn_wrex z F (syn_wbr (.cv z)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_c0c) X)))
      p0016 p0046
  have p0048 :=
    @g_sylbid ph (.classMem (syn_cop (syn_c0c) X) F)
      (syn_wo (.classMem (syn_cop (syn_c0c) X) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex z F
          (syn_wbr (.cv z) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_c0c) X))))
      (.classEq X I) p0008 p0047
  have p0049 :=
    @g_syl5bi (syn_wbr (syn_c0c) F X) (.classMem (syn_cop (syn_c0c) X) F) ph
      (.classEq X I) p0000 p0048
  exact p0049

@[expose]
noncomputable def g_fnfreclem3 (ph : Wff) (z : Var) (F : Class) (G : Class) (I : Class)
    (V : Class) (X : Class) (Y : Class) (dv_F_z : z ∉ F.fv) (dv_G_z : z ∉ G.fv)
    (_dv_I_z : z ∉ I.fv) (dv_X_z : z ∉ X.fv) (dv_Y_z : z ∉ Y.fv) (dv_ph_z : z ∉ ph.fv)
    (hyp_fnfreclem2_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_fnfreclem2_2 : Nominal.NPrf (.imp ph (.classMem G V)))
    (hyp_fnfreclem2_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G))))
    (hyp_fnfreclem2_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G))))
    (hyp_fnfreclem3_5 : Nominal.NPrf (.imp ph (.classMem X (syn_cnnc))))
    (hyp_fnfreclem3_6 : Nominal.NPrf (.imp ph (syn_wbr (syn_cplc X (syn_c1c)) F Y))) :
    Nominal.NPrf
      (.imp ph (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ z } : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv ∪ V.fv ∪ X.fv ∪ Y.fv
  let a : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_I : a ∉ I.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_Y : a ∉ Y.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_t_not_G : t ∉ G.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_Y : t ∉ Y.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a_ne_w : a ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have dv_cache_0001 : t ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0003 : t ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show t ≠ z from (by exact fresh_t_ne_z))
  have dv_cache_0004 : w ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_t, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_cplc (.cv t) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_t, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_not_X, fresh_t_ne_z, fresh_t_not_F, fresh_t_not_Y,
          fresh_t_not_G, or_false, not_false_eq_true])
  have dv_cache_0008 :
    t ∉
      ((syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc X (syn_c1c)) Y)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_not_ph, fresh_t_ne_a,
          fresh_t_not_F, fresh_t_not_X, fresh_t_not_Y, fresh_t_ne_w, fresh_t_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc X (syn_c1c)) Y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_ph_z, fresh_z_ne_a, dv_F_z, dv_X_z,
          dv_Y_z, fresh_z_ne_w, dv_G_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 :
    a ∉ ((syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_X, fresh_a_ne_z, fresh_a_not_F, fresh_a_not_Y,
          fresh_a_not_G, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_ph, not_false_eq_true])
  have dv_cache_0012 : w ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_G, not_false_eq_true])
  have dv_cache_0013 : w ∉ (I).fv :=
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
        simp only [fresh_w_not_I, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cop (syn_cplc X (syn_c1c)) Y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_a_not_X, fresh_a_not_Y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : a ∉ (F).fv :=
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
        simp only [fresh_a_not_F, not_false_eq_true])
  have dv_cache_0016 :
    a ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_w, fresh_a_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_a_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_n_0cex
  have p0001 := @g_opexg (syn_c0c) I (syn_cvv) (syn_cdm G)
  have p0002 :=
    @g_sylancr ph (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cdm G))
      (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0000 hyp_fnfreclem2_3 p0001
  have p0003 :=
    @g_elsnc2g (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I) (syn_cvv)
  have p0004 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I)))
        (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I)))
      p0002 p0003
  have p0005 := @g_opth (syn_cplc X (syn_c1c)) Y (syn_c0c) I
  have p0006 :=
    @g_simplbi (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I))
      (.classEq (syn_cplc X (syn_c1c)) (syn_c0c)) (.classEq Y I) p0005
  have p0007 := @g_n_0cnsuc X
  have p0008 := (Nominal.biimpRefl (syn_wne (syn_cplc X (syn_c1c)) (syn_c0c)))
  have p0009 :=
    @g_mpbi (syn_wne (syn_cplc X (syn_c1c)) (syn_c0c))
      (.neg (.classEq (syn_cplc X (syn_c1c)) (syn_c0c))) p0007 p0008
  have p0010 :=
    @g_pm2_21i (.classEq (syn_cplc X (syn_c1c)) (syn_c0c))
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0009
  have p0011 :=
    @g_a1i
      (.imp (.classEq (syn_cplc X (syn_c1c)) (syn_c0c))
        (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))))
      ph p0010
  have p0012 :=
    @g_syl5 (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I))
      (.classEq (syn_cplc X (syn_c1c)) (syn_c0c)) ph
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0006 p0011
  have p0013 :=
    @g_sylbid ph
      (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I)))
      (.classEq (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_cop (syn_c0c) I))
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0004 p0012
  have p0014 := @g_vex a
  have p0015 := @g_opeqex t z (.cv a) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @g_excom (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) t z
  have p0018 :=
    @g_mpbi (syn_wex t (syn_wex z (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))))
      (syn_wex z (syn_wex t (.classEq (.cv a) (syn_cop (.cv t) (.cv z))))) p0016 p0017
  have p0019 := @g_eleq1 (.cv a) (syn_cop (.cv t) (.cv z)) F
  have p0020 := (Nominal.biimpRefl (syn_wbr (.cv t) F (.cv z)))
  have p0021 :=
    @g_syl6bbr (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (.classMem (.cv a) F)
      (.classMem (syn_cop (.cv t) (.cv z)) F) (syn_wbr (.cv t) F (.cv z)) p0019 p0020
  have p0022 :=
    @g_anbi2d (.classEq (.cv a) (syn_cop (.cv t) (.cv z))) (.classMem (.cv a) F)
      (syn_wbr (.cv t) F (.cv z)) ph p0021
  have p0023 :=
    @g_breq1 (.cv a) (syn_cop (.cv t) (.cv z)) (syn_cop (syn_cplc X (syn_c1c)) Y)
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
  have p0024 :=
    @g_qrpprod (.cv t) (.cv z) (syn_cplc X (syn_c1c)) Y
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0025 := @g_vex t
  have p0026 := @g_addceq1 (.cv w) (.cv t) (syn_c1c)
  have p0027 := @g_eqid (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0028 := @g_n_1cex
  have p0029 := @g_addcex (.cv t) (syn_c1c) p0025 p0028
  have p0030 :=
    @g_fvmpt w (.cv t) (syn_cplc (.cv w) (syn_c1c)) (syn_cplc (.cv t) (syn_c1c)) (syn_cvv)
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0026 p0027 p0029
  have p0031 := Nominal.mp p0025 p0030
  have p0032 :=
    @g_eqeq1i (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv t))
      (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)) p0031
  have p0033 :=
    @g_fnmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv) dv_cache_0006 p0027
  have p0035 := @g_addcexg (.cv w) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_mpan2 (.classMem (.cv w) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cplc (.cv w) (syn_c1c)) (syn_cvv)) p0028 p0035
  have p0037 :=
    @g_mprg (.classMem (syn_cplc (.cv w) (syn_c1c)) (syn_cvv))
      (syn_wfn (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv)) w (syn_cvv)
      p0033 p0036
  have p0038 :=
    @g_fnbrfvb (syn_cvv) (.cv t) (syn_cplc X (syn_c1c))
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
  have p0039 :=
    @g_mp2an (syn_wfn (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv))
      (.classMem (.cv t) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv t))
          (syn_cplc X (syn_c1c)))
        (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_cplc X (syn_c1c))))
      p0037 p0025 p0038
  have p0040 :=
    @g_bitr3i (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
      (.classEq (syn_cfv (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (.cv t))
        (syn_cplc X (syn_c1c)))
      (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
        (syn_cplc X (syn_c1c)))
      p0032 p0039
  have p0041 :=
    @g_anbi1i (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
      (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
        (syn_cplc X (syn_c1c)))
      (syn_wbr (.cv z) G Y) p0040
  have p0042 :=
    @g_bitr4i
      (syn_wbr (syn_cop (.cv t) (.cv z))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) Y))
      (syn_wa (syn_wbr (.cv t) (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_cplc X (syn_c1c))) (syn_wbr (.cv z) G Y))
      (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
        (syn_wbr (.cv z) G Y))
      p0024 p0041
  have p0043 :=
    @g_syl6bb (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))
      (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) Y))
      (syn_wbr (syn_cop (.cv t) (.cv z))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) Y))
      (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
        (syn_wbr (.cv z) G Y))
      p0023 p0042
  have p0044 :=
    @g_anbi12d (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))
      (syn_wa ph (.classMem (.cv a) F)) (syn_wa ph (syn_wbr (.cv t) F (.cv z)))
      (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) Y))
      (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
        (syn_wbr (.cv z) G Y))
      p0022 p0043
  have p0045 := @g_breldm (.cv t) (.cv z) F
  have p0046 :=
    @g_adantl (syn_wbr (.cv t) F (.cv z)) (.classMem (.cv t) (syn_cdm F)) ph p0045
  have p0047 :=
    @g_dmfrec ph F G I V hyp_fnfreclem2_1 hyp_fnfreclem2_2 hyp_fnfreclem2_3
      hyp_fnfreclem2_4
  have p0048 :=
    @g_adantr ph (.classEq (syn_cdm F) (syn_cnnc)) (syn_wbr (.cv t) F (.cv z)) p0047
  have p0049 :=
    @g_eleqtrd (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (.cv t) (syn_cdm F) (syn_cnnc)
      p0046 p0048
  have p0050 :=
    @g_adantr ph (.classMem X (syn_cnnc)) (syn_wbr (.cv t) F (.cv z)) hyp_fnfreclem3_5
  have p0051 := @g_peano4 (.cv t) X
  have p0052 :=
    @g_n_3expia (.classMem (.cv t) (syn_cnnc)) (.classMem X (syn_cnnc))
      (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (.cv t) X)
      p0051
  have p0053 :=
    @g_syl2anc (syn_wa ph (syn_wbr (.cv t) F (.cv z))) (.classMem (.cv t) (syn_cnnc))
      (.classMem X (syn_cnnc))
      (.imp (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (.cv t) X))
      p0049 p0050 p0052
  have p0054 := @g_breq1 (.cv t) X (.cv z) F
  have p0055 :=
    @g_biimpcd (.classEq (.cv t) X) (syn_wbr (.cv t) F (.cv z)) (syn_wbr X F (.cv z))
      p0054
  have p0056 :=
    @g_adantl (syn_wbr (.cv t) F (.cv z))
      (.imp (.classEq (.cv t) X) (syn_wbr X F (.cv z))) ph p0055
  have p0057 :=
    @g_syld (syn_wa ph (syn_wbr (.cv t) F (.cv z)))
      (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (.classEq (.cv t) X)
      (syn_wbr X F (.cv z)) p0053 p0056
  have p0058 :=
    @g_anim1d (syn_wa ph (syn_wbr (.cv t) F (.cv z)))
      (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c))) (syn_wbr X F (.cv z))
      (syn_wbr (.cv z) G Y) p0057
  have p0059 :=
    @g_imp (syn_wa ph (syn_wbr (.cv t) F (.cv z)))
      (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
        (syn_wbr (.cv z) G Y))
      (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) p0058
  have p0060 :=
    @g_syl6bi (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))
      (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) Y)))
      (syn_wa (syn_wa ph (syn_wbr (.cv t) F (.cv z)))
        (syn_wa (.classEq (syn_cplc (.cv t) (syn_c1c)) (syn_cplc X (syn_c1c)))
          (syn_wbr (.cv z) G Y)))
      (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) p0044 p0059
  have p0061 :=
    @g_com12 (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))
      (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) Y)))
      (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) p0060
  have p0062 :=
    @g_exlimdv
      (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) Y)))
      (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))
      (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) t dv_cache_0007 dv_cache_0008
      p0061
  have p0063 :=
    @g_eximdv
      (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) Y)))
      (syn_wex t (.classEq (.cv a) (syn_cop (.cv t) (.cv z))))
      (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)) z dv_cache_0009 p0062
  have p0064 :=
    @g_mpi
      (syn_wa (syn_wa ph (.classMem (.cv a) F)) (syn_wbr (.cv a)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) Y)))
      (syn_wex z (syn_wex t (.classEq (.cv a) (syn_cop (.cv t) (.cv z)))))
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0018 p0063
  have p0065 :=
    @g_ex (syn_wa ph (.classMem (.cv a) F))
      (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) Y))
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) p0064
  have p0066 :=
    @g_rexlimdva ph
      (syn_wbr (.cv a) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) Y))
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y))) a F dv_cache_0010
      dv_cache_0011 p0065
  have p0067 := (Nominal.biimpRefl (syn_wbr (syn_cplc X (syn_c1c)) F Y))
  have p0068 := @g_snex (syn_cop (syn_c0c) I)
  have p0069 := @g_csucex w
  have p0070 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv) V
  have p0071 :=
    @g_sylancr ph
      (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv))
      (.classMem G V)
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      p0069 hyp_fnfreclem2_2 p0070
  have p0072 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I
      dv_cache_0012 dv_cache_0013
  have p0073 :=
    @g_eqtri F (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G))
      hyp_fnfreclem2_1 p0072
  have p0074 :=
    @g_clos1basesucg a (syn_cop (syn_cplc X (syn_c1c)) Y) F
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 p0073
  have p0075 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) F) (syn_wo
          (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I)))
          (syn_wrex a F (syn_wbr (.cv a)
              (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
              (syn_cop (syn_cplc X (syn_c1c)) Y)))))
      p0068 p0071 p0074
  have p0076 :=
    @g_syl5bb (syn_wbr (syn_cplc X (syn_c1c)) F Y)
      (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) F) ph
      (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I)))
        (syn_wrex a F (syn_wbr (.cv a)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc X (syn_c1c)) Y))))
      p0067 p0075
  have p0077 :=
    @g_mpbid ph (syn_wbr (syn_cplc X (syn_c1c)) F Y)
      (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I)))
        (syn_wrex a F (syn_wbr (.cv a)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc X (syn_c1c)) Y))))
      hyp_fnfreclem3_6 p0076
  have p0078 :=
    @g_mpjaod ph
      (.classMem (syn_cop (syn_cplc X (syn_c1c)) Y) (syn_csn (syn_cop (syn_c0c) I)))
      (syn_wex z (syn_wa (syn_wbr X F (.cv z)) (syn_wbr (.cv z) G Y)))
      (syn_wrex a F (syn_wbr (.cv a)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) Y)))
      p0013 p0066 p0077
  exact p0078


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fnfrec (ph : Wff) (F : Class) (G : Class) (I : Class)
    (hyp_fnfrec_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_fnfrec_2 : Nominal.NPrf (.imp ph (.classMem G (syn_cfuns))))
    (hyp_fnfrec_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G))))
    (hyp_fnfrec_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (syn_wfn F (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_ph : b ∉ ph.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
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
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_w_ne_a : w ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_b : w ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have dv_cache_0001 : w ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_F, not_false_eq_true])
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
  have dv_cache_0004 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0005 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : y ∉ ((Wff.classEq (.cv w) (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Wff.classEq (.cv w) (syn_c0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.objEq w t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, or_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.objEq w t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Wff.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Wff.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 :
    b ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
            (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_t, fresh_b_ne_y, fresh_b_not_F, fresh_b_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    a ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
            (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_t, fresh_a_ne_y, fresh_a_not_F, fresh_a_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    y ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
            (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_a, fresh_y_not_F, fresh_y_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
            (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_a, fresh_z_not_F, fresh_z_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : b ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0018 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0019 : z ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show z ≠ a from (by exact fresh_z_ne_a))
  have dv_cache_0020 : y ∉ ((Wff.objEq w x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ ((Wff.objEq w x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ (ph).fv :=
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
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0023 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0024 : y ∉ (G).fv :=
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
        simp only [fresh_y_not_G, not_false_eq_true])
  have dv_cache_0025 : y ∉ (I).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_I, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0027 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0028 :
    y ∉
      ((syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_t, fresh_y_ne_a, fresh_y_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 : z ∉ (G).fv :=
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
        simp only [fresh_z_not_G, not_false_eq_true])
  have dv_cache_0030 : z ∉ (I).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_I, not_false_eq_true])
  have dv_cache_0031 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0032 : z ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_b, not_false_eq_true])
  have dv_cache_0033 :
    z ∉
      ((syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_t, fresh_z_ne_b, fresh_z_not_F,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0034 :
    z ∉ ((syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_y, fresh_z_not_F, fresh_z_ne_a,
          fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0035 :
    y ∉ ((syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_z, fresh_y_not_F, fresh_y_ne_b,
          fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0036 : y ∉ ((Wff.objEq a b)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, or_false, not_false_eq_true])
  have dv_cache_0037 : z ∉ ((Wff.objEq a b)).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, or_false, not_false_eq_true])
  have dv_cache_0038 :
    a ∉
      ((syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
                (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                  (.objEq y z))))))).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_a_not_ph, fresh_a_ne_t,
          fresh_a_ne_y, fresh_a_not_F, fresh_a_ne_z, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0039 :
    b ∉
      ((syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
                (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                  (.objEq y z))))))).fv :=
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
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_b_not_ph, fresh_b_ne_t,
          fresh_b_ne_y, fresh_b_not_F, fresh_b_ne_z, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0040 : w ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0041 :
    w ∉
      ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
              (.objEq y z))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_y,
          fresh_w_not_F, fresh_w_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0042 : t ∉ (ph).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_ph, not_false_eq_true])
  have dv_cache_0043 :
    t ∉
      ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
              (.objEq y z))))).fv :=
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
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_y,
          fresh_t_not_F, fresh_t_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0044 :
    w ∉
      ((Wff.all y (.all z
            (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z)))
              (.objEq y z))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_F,
          fresh_w_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0045 :
    w ∉
      ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
              (.objEq y z))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y,
          fresh_w_not_F, fresh_w_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0046 :
    w ∉
      ((Wff.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
                (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_a,
          fresh_w_not_F, fresh_w_ne_b, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0047 : w ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0048 : x ∉ (ph).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0049 : x ∉ (F).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0050 : x ≠ y :=
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
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0051 : x ≠ z :=
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
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 := @g_breldm (.cv x) (.cv y) F
  have p0001 :=
    @g_adantl (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) (syn_cdm F)) ph p0000
  have p0002 :=
    @g_dmfrec ph F G I (syn_cfuns) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3 hyp_fnfrec_4
  have p0003 :=
    @g_adantr ph (.classEq (syn_cdm F) (syn_cnnc)) (syn_wbr (.cv x) F (.cv y)) p0002
  have p0004 :=
    @g_eleqtrd (syn_wa ph (syn_wbr (.cv x) F (.cv y))) (.cv x) (syn_cdm F) (syn_cnnc)
      p0001 p0003
  have p0005 :=
    @g_adantrr ph (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) (syn_cnnc))
      (syn_wbr (.cv x) F (.cv z)) p0004
  have p0006 := @g_frecexg F G I (syn_cfuns) hyp_fnfrec_1
  have p0007 :=
    @g_fnfreclem1 y z w F (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_n_3syl ph (.classMem G (syn_cfuns)) (.classMem F (syn_cvv))
      (.classMem (.cab w (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
                (.objEq y z))))) (syn_cvv))
      hyp_fnfrec_2 p0006 p0007
  have p0009 := @g_breq1 (.cv w) (syn_c0c) (.cv y) F
  have p0010 := @g_breq1 (.cv w) (syn_c0c) (.cv z) F
  have p0011 :=
    @g_anbi12d (.classEq (.cv w) (syn_c0c)) (syn_wbr (.cv w) F (.cv y))
      (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (.cv w) F (.cv z))
      (syn_wbr (syn_c0c) F (.cv z)) p0009 p0010
  have p0012 :=
    @g_imbi1d (.classEq (.cv w) (syn_c0c))
      (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
      (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z)
      p0011
  have p0013 :=
    @g_n_2albidv (.classEq (.cv w) (syn_c0c))
      (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z))
      y z dv_cache_0007 dv_cache_0008 p0012
  have p0014 := @g_breq1 (.cv w) (.cv t) (.cv y) F
  have p0015 := @g_breq1 (.cv w) (.cv t) (.cv z) F
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w t) (syn_wb (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv t) F (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w t) (syn_wb (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv t) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @g_anbi12d (.objEq w t) (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv t) F (.cv y))
      (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv t) F (.cv z)) p0016_e00_recanon
      p0016_e01_recanon
  have p0017 :=
    @g_imbi1d (.objEq w t)
      (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
      (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z) p0016
  have p0018 :=
    @g_n_2albidv (.objEq w t)
      (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
      y z dv_cache_0009 dv_cache_0010 p0017
  have p0019 := @g_breq1 (.cv w) (syn_cplc (.cv t) (syn_c1c)) (.cv y) F
  have p0020 := @g_breq1 (.cv w) (syn_cplc (.cv t) (syn_c1c)) (.cv z) F
  have p0021 :=
    @g_anbi12d (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c))) (syn_wbr (.cv w) F (.cv y))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (.cv w) F (.cv z))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z)) p0019 p0020
  have p0022 :=
    @g_imbi1d (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))
      (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
      (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z)))
      (.objEq y z) p0021
  have p0023 :=
    @g_n_2albidv (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))
      (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))
      y z dv_cache_0011 dv_cache_0012 p0022
  have p0024 := @g_breq2 (.cv y) (.cv a) (syn_cplc (.cv t) (syn_c1c)) F
  have p0025 := @g_breq2 (.cv z) (.cv b) (syn_cplc (.cv t) (syn_c1c)) F
  have p0026_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y a) (syn_wb (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cplc syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0026_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq z b) (syn_wb (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cplc syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @g_bi2anan9 (.objEq y a) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (.objEq z b)
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) p0026_e00_recanon p0026_e01_recanon
  have p0027 := @g_eqeq12 (.cv y) (.cv a) (.cv z) (.cv b)
  have p0028_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq y a) (.objEq z b)) (syn_wb (.objEq y z) (.objEq a b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0027
  have p0028 :=
    @g_imbi12d (syn_wa (.objEq y a) (.objEq z b))
      (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z)))
      (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))
      (.objEq y z) (.objEq a b) p0026 p0028_e01_recanon
  have p0029 :=
    @g_cbval2v
      (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))
      y z a b dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0006 dv_cache_0019 p0028
  have p0030 :=
    @g_syl6bb (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.objEq y z))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y))
              (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))))
      (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
              (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))))
      p0023 p0029
  have p0031 := @g_breq1 (.cv w) (.cv x) (.cv y) F
  have p0032 := @g_breq1 (.cv w) (.cv x) (.cv z) F
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv x) F (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0033_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv x) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @g_anbi12d (.objEq w x) (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv x) F (.cv y))
      (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv x) F (.cv z)) p0033_e00_recanon
      p0033_e01_recanon
  have p0034 :=
    @g_imbi1d (.objEq w x)
      (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z) p0033
  have p0035 :=
    @g_n_2albidv (.objEq w x)
      (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))
      y z dv_cache_0020 dv_cache_0021 p0034
  have p0036 :=
    @g_fnfreclem2 ph F G I (syn_cfuns) (.cv y) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3
      hyp_fnfrec_4
  have p0037 := @g_imp ph (syn_wbr (syn_c0c) F (.cv y)) (.classEq (.cv y) I) p0036
  have p0038 :=
    @g_adantrr ph (syn_wbr (syn_c0c) F (.cv y)) (.classEq (.cv y) I)
      (syn_wbr (syn_c0c) F (.cv z)) p0037
  have p0039 :=
    @g_fnfreclem2 ph F G I (syn_cfuns) (.cv z) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3
      hyp_fnfrec_4
  have p0040 := @g_imp ph (syn_wbr (syn_c0c) F (.cv z)) (.classEq (.cv z) I) p0039
  have p0041 :=
    @g_adantrl ph (syn_wbr (syn_c0c) F (.cv z)) (.classEq (.cv z) I)
      (syn_wbr (syn_c0c) F (.cv y)) p0040
  have p0042 :=
    @g_eqtr4d
      (syn_wa ph (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))))
      (.cv y) I (.cv z) p0038 p0041
  have p0043_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))))
        (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0042
  have p0043 :=
    @g_ex ph (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z)))
      (.objEq y z) p0043_e00_recanon
  have p0044 :=
    @g_alrimivv ph
      (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z))
      y z dv_cache_0022 dv_cache_0023 p0043
  have p0045 :=
    @g_ad2antrr ph (.classMem G (syn_cfuns)) (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) hyp_fnfrec_2
  have p0046 :=
    @g_ad2antrr ph (.classMem I (syn_cdm G)) (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) hyp_fnfrec_3
  have p0047 :=
    @g_ad2antrr ph (syn_wss (syn_crn G) (syn_cdm G)) (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) hyp_fnfrec_4
  have p0048 :=
    @g_simplr ph (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
  have p0049 :=
    @g_simpr (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
  have p0050 :=
    @g_fnfreclem3
      (syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)))
      y F G I (syn_cfuns) (.cv t) (.cv a) dv_cache_0002 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0028 hyp_fnfrec_1 p0045 p0046 p0047 p0048 p0049
  have p0051 :=
    @g_adantlrr ph (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
      (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))))
      p0050
  have p0052 :=
    @g_ex
      (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
      (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))) p0051
  have p0053 :=
    @g_ad2antrr ph (.classMem G (syn_cfuns)) (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) hyp_fnfrec_2
  have p0054 :=
    @g_ad2antrr ph (.classMem I (syn_cdm G)) (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) hyp_fnfrec_3
  have p0055 :=
    @g_ad2antrr ph (syn_wss (syn_crn G) (syn_cdm G)) (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) hyp_fnfrec_4
  have p0056 :=
    @g_simplr ph (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
  have p0057 :=
    @g_simpr (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
  have p0058 :=
    @g_fnfreclem3
      (syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))
      z F G I (syn_cfuns) (.cv t) (.cv b) dv_cache_0003 dv_cache_0029 dv_cache_0030
      dv_cache_0031 dv_cache_0032 dv_cache_0033 hyp_fnfrec_1 p0053 p0054 p0055 p0056 p0057
  have p0059 :=
    @g_adantlrr ph (.classMem (.cv t) (syn_cnnc))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
      (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))))
      p0058
  have p0060 :=
    @g_ex
      (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
      (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) p0059
  have p0061 :=
    @g_anim12d
      (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
      (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))))
      (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
      (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) p0052
      p0060
  have p0062 :=
    @g_eeanv (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
      (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))) y z dv_cache_0034
      dv_cache_0035
  have p0063 :=
    @g_syl6ibr
      (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))
      (syn_wa (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))))
        (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
            (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))
      p0061 p0062
  have p0064 :=
    @g_n_19_29
      (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
          (.objEq y z)))
      (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
          (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))
      y
  have p0065 :=
    @g_n_19_29
      (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
      (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
        (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))
      z
  have p0066 :=
    @g_eximi
      (syn_wa (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))) (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
            (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))
      (syn_wex z (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))
          (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
            (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))
      y p0065
  have p0067 :=
    @g_syl
      (syn_wa (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
              (.objEq y z)))) (syn_wex y (syn_wex z
            (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
              (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))))
      (syn_wex y (syn_wa (.all z
            (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
              (.objEq y z))) (syn_wex z
            (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
              (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))))
      (syn_wex y (syn_wex z (syn_wa
            (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
            (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
              (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))))
      p0064 p0066
  have p0068 :=
    @g_pm3_35 (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
      (.objEq y z)
  have p0069 := @g_breq1 (.cv y) (.cv z) (.cv a) G
  have p0070_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0069
  have p0070 :=
    @g_anbi1d (.objEq y z) (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv a))
      (syn_wbr (.cv z) G (.cv b)) p0070_e00_recanon
  have p0071 :=
    @g_biimpa (.objEq y z)
      (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b)))
      (syn_wa (syn_wbr (.cv z) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) p0070
  have p0072 := @g_elfunsi G
  have p0073 := @g_funbrfv (.cv z) (.cv a) G
  have p0074 :=
    @g_n_3syl ph (.classMem G (syn_cfuns)) (syn_wfun G)
      (.imp (syn_wbr (.cv z) G (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv a)))
      hyp_fnfrec_2 p0072 p0073
  have p0075 := @g_funbrfv (.cv z) (.cv b) G
  have p0076 :=
    @g_n_3syl ph (.classMem G (syn_cfuns)) (syn_wfun G)
      (.imp (syn_wbr (.cv z) G (.cv b)) (.classEq (syn_cfv G (.cv z)) (.cv b)))
      hyp_fnfrec_2 p0072 p0075
  have p0077 :=
    @g_anim12d ph (syn_wbr (.cv z) G (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv a))
      (syn_wbr (.cv z) G (.cv b)) (.classEq (syn_cfv G (.cv z)) (.cv b)) p0074 p0076
  have p0078 := @g_eqtr2 (syn_cfv G (.cv z)) (.cv a) (.cv b)
  have p0079_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (syn_cfv G (.cv z)) (.cv a))
          (.classEq (syn_cfv G (.cv z)) (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cfv syn_cio syn_cuni syn_wex syn_csn syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0078
  have p0079 :=
    @g_syl56
      (syn_wa (.objEq y z) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))))
      (syn_wa (syn_wbr (.cv z) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) ph
      (syn_wa (.classEq (syn_cfv G (.cv z)) (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv b)))
      (.objEq a b) p0071 p0077 p0079_e02_recanon
  have p0080 :=
    @g_exp3a ph (.objEq y z)
      (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b) p0079
  have p0081 :=
    @g_syl5
      (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
        (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))
      (.objEq y z) ph
      (.imp (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b))
      p0068 p0080
  have p0082 :=
    @g_exp3a ph (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
      (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b))
      p0081
  have p0083 :=
    @g_com34 ph (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
      (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
      (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b) p0082
  have p0084 :=
    @g_imp3a ph (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
      (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b)))
      (.imp (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
        (.objEq a b))
      p0083
  have p0085 :=
    @g_com12 ph
      (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
        (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))))
      (.imp (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
        (.objEq a b))
      p0084
  have p0086 :=
    @g_an4s (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))
      (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))
      (.imp ph (.imp (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z)) (.objEq a b)))
      p0085
  have p0087 :=
    @g_com3l
      (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
        (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))
      ph
      (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
      (.objEq a b) p0086
  have p0088 :=
    @g_imp3a ph
      (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
      (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
        (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))
      (.objEq a b) p0087
  have p0089 :=
    @g_exlimdvv ph
      (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
          (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
          (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))
      (.objEq a b) y z dv_cache_0036 dv_cache_0037 dv_cache_0022 dv_cache_0023 p0088
  have p0090 :=
    @g_adantr ph
      (.imp (syn_wex y (syn_wex z (syn_wa
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))
              (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
                (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))))
        (.objEq a b))
      (.classMem (.cv t) (syn_cnnc)) p0089
  have p0091 :=
    @g_syl5
      (syn_wa (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
              (.objEq y z)))) (syn_wex y (syn_wex z
            (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
              (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))))
      (syn_wex y (syn_wex z (syn_wa
            (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))
            (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
              (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))))
      (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (.objEq a b) p0067 p0090
  have p0092 :=
    @g_exp3a (syn_wa ph (.classMem (.cv t) (syn_cnnc)))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
            (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))
      (.objEq a b) p0091
  have p0093 :=
    @g_impr ph (.classMem (.cv t) (syn_cnnc))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (.imp (syn_wex y (syn_wex z
            (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
              (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) (.objEq a b))
      p0092
  have p0094 :=
    @g_syld
      (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
        (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))
            (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))
      (.objEq a b) p0063 p0093
  have p0095 :=
    @g_alrimivv
      (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
          (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))
      a b dv_cache_0038 dv_cache_0039 p0094
  have p0096 :=
    @g_expr ph (.classMem (.cv t) (syn_cnnc))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
              (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))))
      p0095
  have p0097 :=
    @g_ancoms ph (.classMem (.cv t) (syn_cnnc))
      (.imp (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
              (.objEq y z)))) (.all a (.all b (.imp
              (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
                (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b)))))
      p0096
  have p0098_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv x)) (syn_wb (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
                (.objEq y z)))) (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
                (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0098 :=
    @g_findsd
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z)))
            (.objEq y z))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z)))
            (.objEq y z))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
              (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
            (.objEq y z))))
      ph w t (.cv x) (syn_cvv) dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
      dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 p0008 p0013 p0018 p0030
      p0098_e04_recanon p0044 p0097
  have p0099 :=
    @g_n_19_21bbi (syn_wa (.classMem (.cv x) (syn_cnnc)) ph)
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))
      y z p0098
  have p0100 :=
    @g_ex (.classMem (.cv x) (syn_cnnc)) ph
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))
      p0099
  have p0101 :=
    @g_imp3a (.classMem (.cv x) (syn_cnnc)) ph
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z) p0100
  have p0102 :=
    @g_mpcom (.classMem (.cv x) (syn_cnnc))
      (syn_wa ph (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))))
      (.objEq y z) p0005 p0101
  have p0103 :=
    @g_ex ph (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)
      p0102
  have p0104 :=
    @g_alrimivv ph
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))
      y z dv_cache_0022 dv_cache_0023 p0103
  have p0105 :=
    @g_alrimiv ph
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
            (.objEq y z))))
      x dv_cache_0048 p0104
  have p0106 :=
    @g_dffun2 x y z F dv_cache_0049 dv_cache_0002 dv_cache_0003 dv_cache_0050
      dv_cache_0051 dv_cache_0006
  have p0107 :=
    @g_sylibr ph
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))
              (.objEq y z)))))
      (syn_wfun F) p0105 p0106
  have p0108 := (Nominal.biimpRefl (syn_wfn F (syn_cnnc)))
  have p0109 :=
    @g_sylanbrc ph (syn_wfun F) (.classEq (syn_cdm F) (syn_cnnc)) (syn_wfn F (syn_cnnc))
      p0107 p0002 p0108
  exact p0109


end NFChoice.DirectNominalPrf.WPPReplay

end
