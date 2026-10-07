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

/-- Checked nominal proof certificate identified upstream as `g_frecexg`. -/
@[expose]
noncomputable def gFrecexg (F : Class) (G : Class) (I : Class) (V : Class)
    (hyp_frecex_1 : Nominal.NPrf (.classEq F (synCfrec G I))) :
    Nominal.NPrf (.imp (.classMem G V) (.classMem F (synCvv))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec x G I
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gEqtri F (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      hyp_frecex_1 p0000
  have p0002 := @gSnex (synCop (synC0c) I)
  have p0003 := @gCsucex x
  have p0004 :=
    @gPprodexg (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G (synCvv) V
  have p0005 :=
    @gMpan (.classMem (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (synCvv))
      (.classMem G V)
      (.classMem (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) (synCvv))
      p0003 p0004
  have p0006 :=
    @gClos1exg (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv)
  have p0007 :=
    @gSylancr (.classMem G V) (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) (synCvv))
      (.classMem (synCclos1 (synCsn (synCop (synC0c) I))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)) (synCvv))
      p0002 p0005 p0006
  have p0008 :=
    @gSyl5eqel (.classMem G V) F
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synCvv) p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_frecex`. -/
@[expose]
noncomputable def gFrecex (F : Class) (G : Class) (I : Class)
    (hyp_frecex_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_frecex_2 : Nominal.NPrf (.classMem G (synCvv))) :
    Nominal.NPrf (.classMem F (synCvv)) :=
  by
  have p0000 := @gFrecexg F G I (synCvv) hyp_frecex_1
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

/-- Checked nominal proof certificate identified upstream as `g_frecxp`. -/
@[expose]
noncomputable def gFrecxp (F : Class) (G : Class) (I : Class)
    (hyp_frecxp_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_frecxp_2 : Nominal.NPrf (.classMem G (synCvv))) :
    Nominal.NPrf (synWss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))) :=
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
  have dv_cache_0009 : d ∉ ((synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))).fv :=
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
  have dv_cache_0010 : a ∉ ((synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))).fv :=
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
  have dv_cache_0011 : b ∉ ((synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))).fv :=
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
  have dv_cache_0012 : c ∉ ((synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
          (.classMem (.cv z)
            (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
          (.classMem (.cv z)
            (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
          (.classMem (.cv z)
            (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))).fv :=
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
      ((Wff.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
          (.classMem (.cv z)
            (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))).fv :=
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
  have dv_cache_0031 : y ∉ ((synCfrec G (.cv i))).fv :=
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
  have dv_cache_0032 : z ∉ ((synCfrec G (.cv i))).fv :=
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
    y ∉ ((synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)).fv :=
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
    z ∉ ((synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)).fv :=
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
    y ∉ ((synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))).fv :=
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
    z ∉ ((synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))).fv :=
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
      ((synWss (synCfrec G I) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))).fv :=
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
  have p0000 := @gEqid G
  have p0001 := @gFreceq12 G G (.cv i) I
  have p0002 :=
    @gMpan (.classEq G G) (.classEq (.cv i) I)
      (.classEq (synCfrec G (.cv i)) (synCfrec G I)) p0000 p0001
  have p0003 := @gSneq (.cv i) I
  have p0004 :=
    @gUneq2d (.classEq (.cv i) I) (synCsn (.cv i)) (synCsn I) (synCrn G) p0003
  have p0005 :=
    @gXpeq2d (.classEq (.cv i) I) (synCun (synCrn G) (synCsn (.cv i)))
      (synCun (synCrn G) (synCsn I)) (synCnnc) p0004
  have p0006 :=
    @gSseq12d (.classEq (.cv i) I) (synCfrec G (.cv i)) (synCfrec G I)
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))) p0002 p0005
  have p0007 := @gNncex
  have p0008 := @gRnex G hyp_frecxp_2
  have p0009 := @gSnex (.cv i)
  have p0010 := @gUnex (synCrn G) (synCsn (.cv i)) p0008 p0009
  have p0011 := @gXpex (synCnnc) (synCun (synCrn G) (synCsn (.cv i))) p0007 p0010
  have p0012 := @gPeano1
  have p0013 := @gVex i
  have p0014 := @gSnid (.cv i) p0013
  have p0015 := @gElun2 (.cv i) (synCsn (.cv i)) (synCrn G)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gN0cex
  have p0018 := @gOpex (synC0c) (.cv i) p0017 p0013
  have p0019 :=
    @gSnss (synCop (synC0c) (.cv i))
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))) p0018
  have p0020 :=
    @gOpelxp (synC0c) (.cv i) (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))
  have p0021 :=
    @gBitr3i
      (synWss (synCsn (synCop (synC0c) (.cv i)))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (synCop (synC0c) (.cv i))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWa (.classMem (synC0c) (synCnnc))
        (.classMem (.cv i) (synCun (synCrn G) (synCsn (.cv i)))))
      p0019 p0020
  have p0022 :=
    @gMpbir2an
      (synWss (synCsn (synCop (synC0c) (.cv i)))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (synC0c) (synCnnc))
      (.classMem (.cv i) (synCun (synCrn G) (synCsn (.cv i)))) p0012 p0016 p0021
  have p0023 :=
    @gBrpprod a b c d (.cv y) (.cv z) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))
      G dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
  have p0024 := @gVex a
  have p0025 := @gVex c
  have p0026 := @gBrcsuc x (.cv a) (.cv c) dv_cache_0023 dv_cache_0024 p0024 p0025
  have p0027 := @gBrelrn (.cv b) (.cv d) G
  have p0028 := @gElun1 (.cv d) (synCrn G) (synCsn (.cv i))
  have p0029 :=
    @gSyl (synWbr (.cv b) G (.cv d)) (.classMem (.cv d) (synCrn G))
      (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))) p0027 p0028
  have p0030 := @gPeano2 (.cv a)
  have p0031 :=
    @gAnim12ci (synWbr (.cv b) G (.cv d))
      (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i))))
      (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
      p0029 p0030
  have p0032 :=
    @gAdantrr (synWbr (.cv b) G (.cv d)) (.classMem (.cv a) (synCnnc))
      (synWa (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
        (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))) p0031
  have p0033 := @gEleq1 (.cv c) (synCplc (.cv a) (synC1c)) (synCnnc)
  have p0034 :=
    @gAnbi1d (.classEq (.cv c) (synCplc (.cv a) (synC1c)))
      (.classMem (.cv c) (synCnnc)) (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
      (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))) p0033
  have p0035 :=
    @gSyl5ibr
      (synWa (synWbr (.cv b) G (.cv d)) (synWa (.classMem (.cv a) (synCnnc))
          (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i))))))
      (synWa (.classMem (.cv c) (synCnnc))
        (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classEq (.cv c) (synCplc (.cv a) (synC1c)))
      (synWa (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
        (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))
      p0032 p0034
  have p0036 :=
    @gExp3a (.classEq (.cv c) (synCplc (.cv a) (synC1c))) (synWbr (.cv b) G (.cv d))
      (synWa (.classMem (.cv a) (synCnnc))
        (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWa (.classMem (.cv c) (synCnnc))
        (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))
      p0035
  have p0037 :=
    @gSylbi (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
      (.classEq (.cv c) (synCplc (.cv a) (synC1c)))
      (.imp (synWbr (.cv b) G (.cv d)) (.imp (synWa (.classMem (.cv a) (synCnnc))
            (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))))
          (synWa (.classMem (.cv c) (synCnnc))
            (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))))
      p0026 p0036
  have p0038 :=
    @gImp (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
      (synWbr (.cv b) G (.cv d))
      (.imp (synWa (.classMem (.cv a) (synCnnc))
          (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))))
        (synWa (.classMem (.cv c) (synCnnc))
          (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i))))))
      p0037
  have p0039 :=
    @gEleq1 (.cv y) (synCop (.cv a) (.cv b))
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))
  have p0040 :=
    @gOpelxp (.cv a) (.cv b) (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))
  have p0041 :=
    @gSyl6bb (.classEq (.cv y) (synCop (.cv a) (.cv b)))
      (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (synCop (.cv a) (.cv b))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWa (.classMem (.cv a) (synCnnc))
        (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))))
      p0039 p0040
  have p0042 :=
    @gAdantr (.classEq (.cv y) (synCop (.cv a) (.cv b)))
      (synWb (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (synWa (.classMem (.cv a) (synCnnc))
          (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i))))))
      (.classEq (.cv z) (synCop (.cv c) (.cv d))) p0041
  have p0043 :=
    @gEleq1 (.cv z) (synCop (.cv c) (.cv d))
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))
  have p0044 :=
    @gOpelxp (.cv c) (.cv d) (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))
  have p0045 :=
    @gSyl6bb (.classEq (.cv z) (synCop (.cv c) (.cv d)))
      (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (synCop (.cv c) (.cv d))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWa (.classMem (.cv c) (synCnnc))
        (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))
      p0043 p0044
  have p0046 :=
    @gAdantl (.classEq (.cv z) (synCop (.cv c) (.cv d)))
      (synWb (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (synWa (.classMem (.cv c) (synCnnc))
          (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i))))))
      (.classEq (.cv y) (synCop (.cv a) (.cv b))) p0045
  have p0047 :=
    @gImbi12d
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWa (.classMem (.cv a) (synCnnc))
        (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWa (.classMem (.cv c) (synCnnc))
        (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i)))))
      p0042 p0046
  have p0048 :=
    @gSyl5ibr
      (synWa (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
        (synWbr (.cv b) G (.cv d)))
      (.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))
      (synWa (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))))
      (.imp (synWa (.classMem (.cv a) (synCnnc))
          (.classMem (.cv b) (synCun (synCrn G) (synCsn (.cv i)))))
        (synWa (.classMem (.cv c) (synCnnc))
          (.classMem (.cv d) (synCun (synCrn G) (synCsn (.cv i))))))
      p0038 p0047
  have p0049 :=
    @gN3impia (.classEq (.cv y) (synCop (.cv a) (.cv b)))
      (.classEq (.cv z) (synCop (.cv c) (.cv d)))
      (synWa (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
        (synWbr (.cv b) G (.cv d)))
      (.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))
      p0048
  have p0050 :=
    @gExlimivv
      (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
        (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWa
          (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
          (synWbr (.cv b) G (.cv d))))
      (.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))
      c d dv_cache_0025 dv_cache_0026 p0049
  have p0051 :=
    @gExlimivv
      (synWex c (synWex d (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
            (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWa
              (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
              (synWbr (.cv b) G (.cv d))))))
      (.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))
      a b dv_cache_0027 dv_cache_0028 p0050
  have p0052 :=
    @gSylbi
      (synWbr (.cv y) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
        (.cv z))
      (synWex a (synWex b (synWex c (synWex d
              (synW3a (.classEq (.cv y) (synCop (.cv a) (.cv b)))
                (.classEq (.cv z) (synCop (.cv c) (.cv d))) (synWa
                  (synWbr (.cv a) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (.cv c))
                  (synWbr (.cv b) G (.cv d))))))))
      (.imp (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
        (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))
      p0023 p0051
  have p0053 :=
    @gImpcom
      (synWbr (.cv y) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
        (.cv z))
      (.classMem (.cv y) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      p0052
  have p0054 := Nominal.gen p0053 z
  have p0055 :=
    @gRgenw
      (.all z (.imp (synWa (.classMem (.cv y)
              (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))) (synWbr (.cv y)
              (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) (.cv z)))
          (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))))
      y (synCfrec G (.cv i)) p0054
  have p0056 := @gSnex (synCop (synC0c) (.cv i))
  have p0057 := @gCsucex x
  have p0058 :=
    @gPprodex (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G p0057 hyp_frecxp_2
  have p0059 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec x G (.cv i)
      dv_cache_0029 dv_cache_0030
  have p0060 :=
    @gClos1induct y z (synCfrec G (.cv i))
      (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
      (synCsn (synCop (synC0c) (.cv i))) (synCvv)
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))) dv_cache_0031
      dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
      p0056 p0058 p0059
  have p0061 :=
    @gMp3an
      (.classMem (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))) (synCvv))
      (synWss (synCsn (synCop (synC0c) (.cv i)))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWral y (synCfrec G (.cv i)) (.all z (.imp (synWa (.classMem (.cv y)
                (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))) (synWbr (.cv y)
                (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) (.cv z)))
            (.classMem (.cv z) (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i))))))))
      (synWss (synCfrec G (.cv i))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      p0011 p0022 p0055 p0060
  have p0062 :=
    @gVtoclg
      (synWss (synCfrec G (.cv i))
        (synCxp (synCnnc) (synCun (synCrn G) (synCsn (.cv i)))))
      (synWss (synCfrec G I) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))) i I
      (synCvv) dv_cache_0038 dv_cache_0039 p0006 p0061
  have p0063 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec x G I
      dv_cache_0029 dv_cache_0040
  have p0064 := @gOpexb (synC0c) I
  have p0065 :=
    @gSimprbi (.classMem (synCop (synC0c) I) (synCvv)) (.classMem (synC0c) (synCvv))
      (.classMem I (synCvv)) p0064
  have p0066 :=
    @gCon3i (.classMem (synCop (synC0c) I) (synCvv)) (.classMem I (synCvv)) p0065
  have p0067 := @gSnprc (synCop (synC0c) I)
  have p0068 :=
    @gSylib (.neg (.classMem I (synCvv)))
      (.neg (.classMem (synCop (synC0c) I) (synCvv)))
      (.classEq (synCsn (synCop (synC0c) I)) (synC0)) p0066 p0067
  have p0069 :=
    @gClos1eq1 (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synC0)
  have p0070 :=
    @gSyl (.neg (.classMem I (synCvv)))
      (.classEq (synCsn (synCop (synC0c) I)) (synC0))
      (.classEq (synCclos1 (synCsn (synCop (synC0c) I))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
        (synCclos1 (synC0)
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)))
      p0068 p0069
  have p0071 :=
    @gEqid
      (synCclos1 (synC0) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
  have p0072 :=
    @gClos10
      (synCclos1 (synC0) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) p0058 p0071
  have p0073 :=
    @gSyl6eq (.neg (.classMem I (synCvv)))
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synCclos1 (synC0) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synC0) p0070 p0072
  have p0074 := @gN0ss (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))
  have p0075 :=
    @gSyl6eqss (.neg (.classMem I (synCvv)))
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synC0) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))) p0073 p0074
  have p0076 :=
    @gSyl5eqss (.neg (.classMem I (synCvv))) (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))) p0063 p0075
  have p0077 :=
    @gPm261i (.classMem I (synCvv))
      (synWss (synCfrec G I) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))
      p0062 p0076
  have p0078 :=
    @gEqsstri F (synCfrec G I) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))
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

/-- Checked nominal proof certificate identified upstream as `g_frecxpg`. -/
@[expose]
noncomputable def gFrecxpg (F : Class) (G : Class) (I : Class) (V : Class)
    (hyp_frecxpg_1 : Nominal.NPrf (.classEq F (synCfrec G I))) :
    Nominal.NPrf
      (.imp (.classMem G V)
        (synWss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))) :=
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
      ((synWss (synCfrec G I) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))).fv :=
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
  have p0000 := @gEqid I
  have p0001 := @gFreceq12 (.cv g) G I I
  have p0002 :=
    @gMpan2 (.classEq (.cv g) G) (.classEq I I)
      (.classEq (synCfrec (.cv g) I) (synCfrec G I)) p0000 p0001
  have p0003 := @gRneq (.cv g) G
  have p0004 :=
    @gUneq1d (.classEq (.cv g) G) (synCrn (.cv g)) (synCrn G) (synCsn I) p0003
  have p0005 :=
    @gXpeq2d (.classEq (.cv g) G) (synCun (synCrn (.cv g)) (synCsn I))
      (synCun (synCrn G) (synCsn I)) (synCnnc) p0004
  have p0006 :=
    @gSseq12d (.classEq (.cv g) G) (synCfrec (.cv g) I) (synCfrec G I)
      (synCxp (synCnnc) (synCun (synCrn (.cv g)) (synCsn I)))
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))) p0002 p0005
  have p0007 := @gEqid (synCfrec (.cv g) I)
  have p0008 := @gVex g
  have p0009 := @gFrecxp (synCfrec (.cv g) I) (.cv g) I p0007 p0008
  have p0010 :=
    @gVtoclg
      (synWss (synCfrec (.cv g) I)
        (synCxp (synCnnc) (synCun (synCrn (.cv g)) (synCsn I))))
      (synWss (synCfrec G I) (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))) g G
      V dv_cache_0001 dv_cache_0002 p0006 p0009
  have p0011 :=
    @gSyl5eqss (.classMem G V) F (synCfrec G I)
      (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))) hyp_frecxpg_1 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_dmfrec`. -/
@[expose]
noncomputable def gDmfrec (ph : Wff) (F : Class) (G : Class) (I : Class) (V : Class)
    (hyp_dmfrec_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_dmfrec_2 : Nominal.NPrf (.imp ph (.classMem G V)))
    (hyp_dmfrec_3 : Nominal.NPrf (.imp ph (.classMem I (synCdm G))))
    (hyp_dmfrec_4 : Nominal.NPrf (.imp ph (synWss (synCrn G) (synCdm G)))) :
    Nominal.NPrf (.imp ph (.classEq (synCdm F) (synCnnc))) :=
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
  have dv_cache_0003 : t ∉ ((synCop (synC0c) I)).fv :=
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
    t ∉ ((synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)).fv :=
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
  have dv_cache_0006 : t ∉ ((synCsn (synCop (synC0c) I))).fv :=
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
  have dv_cache_0009 : t ∉ ((synCop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0010 : t ∉ ((Wff.classMem (.cv y) (synCdm G))).fv :=
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
  have dv_cache_0015 : w ∉ ((synCplc (.cv x) (synC1c))).fv :=
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
  have dv_cache_0016 : z ∉ ((Wff.classMem (synCop (.cv x) (.cv y)) F)).fv :=
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
  have dv_cache_0017 : z ∉ ((synCplc (.cv x) (synC1c))).fv :=
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
  have dv_cache_0019 : y ∉ ((Wff.classMem (synCplc (.cv x) (synC1c)) (synCdm F))).fv :=
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
  have dv_cache_0022 : x ∉ ((synCdm F)).fv :=
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
  have p0000 := @gFrecxpg F G I V hyp_dmfrec_1
  have p0001 := @gDmss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))
  have p0002 :=
    @gN3syl ph (.classMem G V)
      (synWss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))
      (synWss (synCdm F) (synCdm (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))))
      hyp_dmfrec_2 p0000 p0001
  have p0003 := @gDmxpss (synCnnc) (synCun (synCrn G) (synCsn I))
  have p0004 :=
    @gSyl6ss ph (synCdm F)
      (synCdm (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))) (synCnnc) p0002
      p0003
  have p0005 := @gFrecexg F G I V hyp_dmfrec_1
  have p0006 := @gSyl ph (.classMem G V) (.classMem F (synCvv)) hyp_dmfrec_2 p0005
  have p0007 := @gDmexg F (synCvv)
  have p0008 :=
    @gSyl ph (.classMem F (synCvv)) (.classMem (synCdm F) (synCvv)) p0006 p0007
  have p0009 := @gN0cex
  have p0010 := @gOpexg (synC0c) I (synCvv) (synCdm G)
  have p0011 :=
    @gMpan (.classMem (synC0c) (synCvv)) (.classMem I (synCdm G))
      (.classMem (synCop (synC0c) I) (synCvv)) p0009 p0010
  have p0012 :=
    @gSyl ph (.classMem I (synCdm G)) (.classMem (synCop (synC0c) I) (synCvv))
      hyp_dmfrec_3 p0011
  have p0013 := @gSnidg (synCop (synC0c) I) (synCvv)
  have p0014 :=
    @gSyl ph (.classMem (synCop (synC0c) I) (synCvv))
      (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I))) p0012 p0013
  have p0015 :=
    @gOrcd ph (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I)))
      (synWrex t F (synWbr (.cv t)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synC0c) I)))
      p0014
  have p0016 := @gSnex (synCop (synC0c) I)
  have p0017 := @gCsucex w
  have p0018 :=
    @gPprodexg (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G (synCvv) V
  have p0019 :=
    @gMpan (.classMem (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv))
      (.classMem G V)
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      p0017 p0018
  have p0020 :=
    @gSyl ph (.classMem G V)
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      hyp_dmfrec_2 p0019
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec w G I
      dv_cache_0001 dv_cache_0002
  have p0022 :=
    @gEqtri F (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G))
      hyp_dmfrec_1 p0021
  have p0023 :=
    @gClos1basesucg t (synCop (synC0c) I) F
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0022
  have p0024 :=
    @gSylancr ph (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      (synWb (.classMem (synCop (synC0c) I) F)
        (synWo (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I))) (synWrex t F
            (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
              (synCop (synC0c) I)))))
      p0016 p0020 p0023
  have p0025 :=
    @gMpbird ph (.classMem (synCop (synC0c) I) F)
      (synWo (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I))) (synWrex t F
          (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synC0c) I))))
      p0015 p0024
  have p0026 := @gOpeldm (synC0c) I F
  have p0027 :=
    @gSyl ph (.classMem (synCop (synC0c) I) F) (.classMem (synC0c) (synCdm F)) p0025
      p0026
  have p0028 := @gEldm2 y (.cv x) F dv_cache_0007 dv_cache_0008
  have p0029 :=
    @gClos1basesucg t (synCop (.cv x) (.cv y)) F
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv) dv_cache_0009 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0022
  have p0030 :=
    @gSylancr ph (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      (synWb (.classMem (synCop (.cv x) (.cv y)) F)
        (synWo (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop (synC0c) I)))
          (synWrex t F (synWbr (.cv t)
              (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
              (synCop (.cv x) (.cv y))))))
      p0016 p0020 p0029
  have p0031 := @gVex x
  have p0032 := @gVex y
  have p0033 := @gOpex (.cv x) (.cv y) p0031 p0032
  have p0034 := @gElsnc (synCop (.cv x) (.cv y)) (synCop (synC0c) I) p0033
  have p0035 := @gOpth (.cv x) (.cv y) (synC0c) I
  have p0036 :=
    @gBitri (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop (synC0c) I)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop (synC0c) I))
      (synWa (.classEq (.cv x) (synC0c)) (.classEq (.cv y) I)) p0034 p0035
  have p0037 :=
    @gSimprbi (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop (synC0c) I)))
      (.classEq (.cv x) (synC0c)) (.classEq (.cv y) I) p0036
  have p0038 := @gEleq1 (.cv y) I (synCdm G)
  have p0039 :=
    @gBiimprcd (.classEq (.cv y) I) (.classMem (.cv y) (synCdm G))
      (.classMem I (synCdm G)) p0038
  have p0040 :=
    @gSyl ph (.classMem I (synCdm G))
      (.imp (.classEq (.cv y) I) (.classMem (.cv y) (synCdm G))) hyp_dmfrec_3 p0039
  have p0041 :=
    @gSyl5 (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop (synC0c) I)))
      (.classEq (.cv y) I) ph (.classMem (.cv y) (synCdm G)) p0037 p0040
  have p0042 := @gOpeq (.cv t)
  have p0043 :=
    @gBreq1i (.cv t) (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t)))
      (synCop (.cv x) (.cv y))
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) p0042
  have p0044 :=
    @gQrpprod (synCproj1 (.cv t)) (synCproj2 (.cv t)) (.cv x) (.cv y)
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G
  have p0045 :=
    @gBitri
      (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (.cv x) (.cv y)))
      (synWbr (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t)))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (.cv x) (.cv y)))
      (synWa (synWbr (synCproj1 (.cv t)) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (.cv x)) (synWbr (synCproj2 (.cv t)) G (.cv y)))
      p0043 p0044
  have p0046 :=
    @gSimprbi
      (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (.cv x) (.cv y)))
      (synWbr (synCproj1 (.cv t)) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (.cv x))
      (synWbr (synCproj2 (.cv t)) G (.cv y)) p0045
  have p0047 := @gBrelrn (synCproj2 (.cv t)) (.cv y) G
  have p0048 :=
    @gSyl
      (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (.cv x) (.cv y)))
      (synWbr (synCproj2 (.cv t)) G (.cv y)) (.classMem (.cv y) (synCrn G)) p0046 p0047
  have p0049 := @gSseld ph (synCrn G) (synCdm G) (.cv y) hyp_dmfrec_4
  have p0050 :=
    @gSyl5
      (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (.cv x) (.cv y)))
      (.classMem (.cv y) (synCrn G)) ph (.classMem (.cv y) (synCdm G)) p0048 p0049
  have p0051 :=
    @gAdantr ph
      (.imp (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (.cv x) (.cv y))) (.classMem (.cv y) (synCdm G)))
      (.classMem (.cv t) F) p0050
  have p0052 :=
    @gRexlimdva ph
      (synWbr (.cv t) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (.cv x) (.cv y)))
      (.classMem (.cv y) (synCdm G)) t F dv_cache_0010 dv_cache_0011 p0051
  have p0053 :=
    @gJaod ph (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop (synC0c) I)))
      (.classMem (.cv y) (synCdm G))
      (synWrex t F (synWbr (.cv t)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (.cv x) (.cv y))))
      p0041 p0052
  have p0054 :=
    @gSylbid ph (.classMem (synCop (.cv x) (.cv y)) F)
      (synWo (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop (synC0c) I)))
        (synWrex t F (synWbr (.cv t)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (.cv x) (.cv y)))))
      (.classMem (.cv y) (synCdm G)) p0030 p0053
  have p0055 :=
    @gAncld ph (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv y) (synCdm G))
      p0054
  have p0056 :=
    @gClos1conn (synCop (.cv x) (.cv y)) (synCop (synCplc (.cv x) (synC1c)) (.cv z))
      F (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) p0022
  have p0057 :=
    @gEximi
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (synWbr (synCop (.cv x) (.cv y))
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc (.cv x) (synC1c)) (.cv z))))
      (.classMem (synCop (synCplc (.cv x) (synC1c)) (.cv z)) F) z p0056
  have p0058 := @gEldm z (.cv y) G dv_cache_0012 dv_cache_0013
  have p0059 := @gEqid (synCplc (.cv x) (synC1c))
  have p0060 := @gN1cex
  have p0061 := @gAddcex (.cv x) (synC1c) p0031 p0060
  have p0062 :=
    @gBrcsuc w (.cv x) (synCplc (.cv x) (synC1c)) dv_cache_0014 dv_cache_0015 p0031
      p0061
  have p0063 :=
    @gMpbir
      (synWbr (.cv x) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
        (synCplc (.cv x) (synC1c)))
      (.classEq (synCplc (.cv x) (synC1c)) (synCplc (.cv x) (synC1c))) p0059 p0062
  have p0064 :=
    @gQrpprod (.cv x) (.cv y) (synCplc (.cv x) (synC1c)) (.cv z)
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G
  have p0065 :=
    @gMpbiran
      (synWbr (synCop (.cv x) (.cv y))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc (.cv x) (synC1c)) (.cv z)))
      (synWbr (.cv x) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
        (synCplc (.cv x) (synC1c)))
      (synWbr (.cv y) G (.cv z)) p0063 p0064
  have p0066 :=
    @gExbii
      (synWbr (synCop (.cv x) (.cv y))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc (.cv x) (synC1c)) (.cv z)))
      (synWbr (.cv y) G (.cv z)) z p0065
  have p0067 :=
    @gBitr4i (.classMem (.cv y) (synCdm G)) (synWex z (synWbr (.cv y) G (.cv z)))
      (synWex z (synWbr (synCop (.cv x) (.cv y))
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc (.cv x) (synC1c)) (.cv z))))
      p0058 p0066
  have p0068 :=
    @gAnbi2i (.classMem (.cv y) (synCdm G))
      (synWex z (synWbr (synCop (.cv x) (.cv y))
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc (.cv x) (synC1c)) (.cv z))))
      (.classMem (synCop (.cv x) (.cv y)) F) p0067
  have p0069 :=
    @gN1942v (.classMem (synCop (.cv x) (.cv y)) F)
      (synWbr (synCop (.cv x) (.cv y))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc (.cv x) (synC1c)) (.cv z)))
      z dv_cache_0016
  have p0070 :=
    @gBitr4i
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv y) (synCdm G)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (synWex z
          (synWbr (synCop (.cv x) (.cv y))
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc (.cv x) (synC1c)) (.cv z)))))
      (synWex z (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (synWbr (synCop (.cv x) (.cv y))
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc (.cv x) (synC1c)) (.cv z)))))
      p0068 p0069
  have p0071 := @gEldm2 z (synCplc (.cv x) (synC1c)) F dv_cache_0017 dv_cache_0018
  have p0072 :=
    @gN3imtr4i
      (synWex z (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (synWbr (synCop (.cv x) (.cv y))
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc (.cv x) (synC1c)) (.cv z)))))
      (synWex z (.classMem (synCop (synCplc (.cv x) (synC1c)) (.cv z)) F))
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv y) (synCdm G)))
      (.classMem (synCplc (.cv x) (synC1c)) (synCdm F)) p0057 p0070 p0071
  have p0073 :=
    @gSyl6 ph (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv y) (synCdm G)))
      (.classMem (synCplc (.cv x) (synC1c)) (synCdm F)) p0055 p0072
  have p0074 :=
    @gExlimdv ph (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (synCplc (.cv x) (synC1c)) (synCdm F)) y dv_cache_0019 dv_cache_0020
      p0073
  have p0075 :=
    @gSyl5bi (.classMem (.cv x) (synCdm F))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) F)) ph
      (.classMem (synCplc (.cv x) (synC1c)) (synCdm F)) p0028 p0074
  have p0076 :=
    @gRalrimivw ph
      (.imp (.classMem (.cv x) (synCdm F))
        (.classMem (synCplc (.cv x) (synC1c)) (synCdm F)))
      x (synCnnc) dv_cache_0021 p0075
  have p0077 := @gPeano5 x (synCdm F) (synCvv) dv_cache_0022
  have p0078 :=
    @gSyl3anc ph (.classMem (synCdm F) (synCvv)) (.classMem (synC0c) (synCdm F))
      (synWral x (synCnnc) (.imp (.classMem (.cv x) (synCdm F))
          (.classMem (synCplc (.cv x) (synC1c)) (synCdm F))))
      (synWss (synCnnc) (synCdm F)) p0008 p0027 p0076 p0077
  have p0079 := @gEqssd ph (synCdm F) (synCnnc) p0004 p0078
  exact p0079

/-- Checked nominal proof certificate identified upstream as `g_fnfreclem1`. -/
@[expose]
noncomputable def gFnfreclem1 (y : Var) (z : Var) (w : Var) (F : Class) (V : Class)
    (dv_F_w : w ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_w_y : w ≠ y)
    (dv_w_z : w ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.classMem F V) (.classMem (.cab w (.all y (.all z
                (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
                  (.objEq y z))))) (synCvv))) :=
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
      ((synCrn (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid))))).fv :=
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
  have dv_cache_0003 : z ∉ ((synCop (.cv y) (.cv w))).fv :=
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
      ((synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid)))).fv :=
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
      ((synCcompl (synCrn (synCrn (synCdif
                (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
                (synCins3 (synCid))))))).fv :=
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
  have p0000 := @gVex w
  have p0001 :=
    @gElcompl (.cv w)
      (synCrn (synCrn
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))))
      p0000
  have p0002 :=
    @gElrn2 y (.cv w)
      (synCrn (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid))))
      dv_cache_0001 dv_cache_0002
  have p0003 :=
    @gElrn2 z (synCop (.cv y) (.cv w))
      (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
        (synCins3 (synCid)))
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gEldif (synCop (.cv z) (synCop (.cv y) (.cv w)))
      (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
      (synCins3 (synCid))
  have p0005 :=
    @gElin (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCxp (synCvv) (synCcnv F))
      (synCins2 (synCcnv F))
  have p0006 := @gOpelcnv (.cv y) (.cv w) F
  have p0007 := @gVex z
  have p0008 := @gOpelxp (.cv z) (synCop (.cv y) (.cv w)) (synCvv) (synCcnv F)
  have p0009 :=
    @gMpbiran
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCxp (synCvv) (synCcnv F)))
      (.classMem (.cv z) (synCvv)) (.classMem (synCop (.cv y) (.cv w)) (synCcnv F))
      p0007 p0008
  have p0010 := (Nominal.biimpRefl (synWbr (.cv w) F (.cv y)))
  have p0011 :=
    @gN3bitr4i (.classMem (synCop (.cv y) (.cv w)) (synCcnv F))
      (.classMem (synCop (.cv w) (.cv y)) F)
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCxp (synCvv) (synCcnv F)))
      (synWbr (.cv w) F (.cv y)) p0006 p0009 p0010
  have p0012 := @gOpelcnv (.cv z) (.cv w) F
  have p0013 := @gVex y
  have p0014 := @gOtelins2 (.cv z) (.cv y) (.cv w) (synCcnv F) p0013
  have p0015 := (Nominal.biimpRefl (synWbr (.cv w) F (.cv z)))
  have p0016 :=
    @gN3bitr4i (.classMem (synCop (.cv z) (.cv w)) (synCcnv F))
      (.classMem (synCop (.cv w) (.cv z)) F)
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins2 (synCcnv F)))
      (synWbr (.cv w) F (.cv z)) p0012 p0014 p0015
  have p0017 :=
    @gAnbi12i
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCxp (synCvv) (synCcnv F)))
      (synWbr (.cv w) F (.cv y))
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins2 (synCcnv F)))
      (synWbr (.cv w) F (.cv z)) p0011 p0016
  have p0018 :=
    @gBitri
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
        (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F))))
      (synWa (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
          (synCxp (synCvv) (synCcnv F)))
        (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins2 (synCcnv F))))
      (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z))) p0005 p0017
  have p0019 := @gOtelins3 (.cv z) (.cv y) (.cv w) (synCid) p0000
  have p0020 := (Nominal.biimpRefl (synWbr (.cv z) (synCid) (.cv y)))
  have p0021 := @gIdeq (.cv z) (.cv y) p0013
  have p0022 := @gEqucom z y
  have p0023_e00_recanon :
    Nominal.NPrf (synWb (synWbr (.cv z) (synCid) (.cv y)) (.objEq z y)) :=
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
      p0021
  have p0023 :=
    @gBitri (synWbr (.cv z) (synCid) (.cv y)) (.objEq z y) (.objEq y z)
      p0023_e00_recanon p0022
  have p0024 :=
    @gN3bitr2i
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins3 (synCid)))
      (.classMem (synCop (.cv z) (.cv y)) (synCid)) (synWbr (.cv z) (synCid) (.cv y))
      (.objEq y z) p0019 p0020 p0023
  have p0025 :=
    @gNotbii
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins3 (synCid)))
      (.objEq y z) p0024
  have p0026 :=
    @gAnbi12i
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
        (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F))))
      (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
      (.neg (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins3 (synCid))))
      (.neg (.objEq y z)) p0018 p0025
  have p0027 :=
    @gBitri
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
        (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid))))
      (synWa (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
          (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))) (.neg
          (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w))) (synCins3 (synCid)))))
      (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
        (.neg (.objEq y z)))
      p0004 p0026
  have p0028 :=
    @gExbii
      (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
        (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid))))
      (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
        (.neg (.objEq y z)))
      z p0027
  have p0029 :=
    @gBitri
      (.classMem (synCop (.cv y) (.cv w)) (synCrn
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))))
      (synWex z (.classMem (synCop (.cv z) (synCop (.cv y) (.cv w)))
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))))
      (synWex z (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
          (.neg (.objEq y z))))
      p0003 p0028
  have p0030 :=
    @gExbii
      (.classMem (synCop (.cv y) (.cv w)) (synCrn
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))))
      (synWex z (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
          (.neg (.objEq y z))))
      y p0029
  have p0031 :=
    @gExanali (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
      (.objEq y z) z
  have p0032 :=
    @gExbii
      (synWex z (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
          (.neg (.objEq y z))))
      (.neg (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.objEq y z))))
      y p0031
  have p0033 :=
    @gExnal
      (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
          (.objEq y z)))
      y
  have p0034 :=
    @gBitri
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.neg (.objEq y z)))))
      (synWex y (.neg (.all z
            (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      (.neg (.all y (.all z
            (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      p0032 p0033
  have p0035 :=
    @gN3bitrri
      (.classMem (.cv w) (synCrn (synCrn
            (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
              (synCins3 (synCid))))))
      (synWex y (.classMem (synCop (.cv y) (.cv w)) (synCrn
            (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
              (synCins3 (synCid))))))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.neg (.objEq y z)))))
      (.neg (.all y (.all z
            (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      p0002 p0030 p0034
  have p0036 :=
    @gCon1bii
      (.all y (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.objEq y z))))
      (.classMem (.cv w) (synCrn (synCrn
            (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
              (synCins3 (synCid))))))
      p0035
  have p0037 :=
    @gBitri
      (.classMem (.cv w) (synCcompl (synCrn (synCrn (synCdif
                (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
                (synCins3 (synCid)))))))
      (.neg (.classMem (.cv w) (synCrn (synCrn (synCdif
                (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
                (synCins3 (synCid)))))))
      (.all y (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.objEq y z))))
      p0001 p0036
  have p0038 :=
    @gEqabi
      (.all y (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.objEq y z))))
      w
      (synCcompl (synCrn (synCrn
            (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
              (synCins3 (synCid))))))
      dv_cache_0005 p0037
  have p0039 := @gVvex
  have p0040 := @gCnvexg F V
  have p0041 := @gXpexg (synCvv) (synCcnv F) (synCvv) (synCvv)
  have p0042 :=
    @gSylancr (.classMem F V) (.classMem (synCvv) (synCvv))
      (.classMem (synCcnv F) (synCvv))
      (.classMem (synCxp (synCvv) (synCcnv F)) (synCvv)) p0039 p0040 p0041
  have p0043 := @gIns2exg (synCcnv F) (synCvv)
  have p0044 :=
    @gSyl (.classMem F V) (.classMem (synCcnv F) (synCvv))
      (.classMem (synCins2 (synCcnv F)) (synCvv)) p0040 p0043
  have p0045 :=
    @gInexg (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)) (synCvv) (synCvv)
  have p0046 :=
    @gSyl2anc (.classMem F V) (.classMem (synCxp (synCvv) (synCcnv F)) (synCvv))
      (.classMem (synCins2 (synCcnv F)) (synCvv))
      (.classMem (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F))) (synCvv))
      p0042 p0044 p0045
  have p0047 := @gIdex
  have p0048 := @gIns3ex (synCid) p0047
  have p0049 :=
    @gDifexg (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
      (synCins3 (synCid)) (synCvv) (synCvv)
  have p0050 :=
    @gMpan2
      (.classMem (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F))) (synCvv))
      (.classMem (synCins3 (synCid)) (synCvv))
      (.classMem (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid))) (synCvv))
      p0048 p0049
  have p0051 :=
    @gRnexg
      (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
        (synCins3 (synCid)))
      (synCvv)
  have p0052 :=
    @gN3syl (.classMem F V)
      (.classMem (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F))) (synCvv))
      (.classMem (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid))) (synCvv))
      (.classMem (synCrn
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))) (synCvv))
      p0046 p0050 p0051
  have p0053 :=
    @gRnexg
      (synCrn (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
          (synCins3 (synCid))))
      (synCvv)
  have p0054 :=
    @gComplexg
      (synCrn (synCrn
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))))
      (synCvv)
  have p0055 :=
    @gN3syl (.classMem F V)
      (.classMem (synCrn
          (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
            (synCins3 (synCid)))) (synCvv))
      (.classMem (synCrn (synCrn
            (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
              (synCins3 (synCid))))) (synCvv))
      (.classMem (synCcompl (synCrn (synCrn (synCdif
                (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
                (synCins3 (synCid)))))) (synCvv))
      p0052 p0053 p0054
  have p0056 :=
    @gSyl5eqelr (.classMem F V)
      (.cab w (.all y (.all z
            (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
              (.objEq y z)))))
      (synCcompl (synCrn (synCrn
            (synCdif (synCin (synCxp (synCvv) (synCcnv F)) (synCins2 (synCcnv F)))
              (synCins3 (synCid))))))
      (synCvv) p0038 p0055
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

/-- Checked nominal proof certificate identified upstream as `g_fnfreclem2`. -/
@[expose]
noncomputable def gFnfreclem2 (ph : Wff) (F : Class) (G : Class) (I : Class) (V : Class)
    (X : Class) (hyp_fnfreclem2_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_fnfreclem2_2 : Nominal.NPrf (.imp ph (.classMem G V)))
    (hyp_fnfreclem2_3 : Nominal.NPrf (.imp ph (.classMem I (synCdm G))))
    (_hyp_fnfreclem2_4 : Nominal.NPrf (.imp ph (synWss (synCrn G) (synCdm G)))) :
    Nominal.NPrf (.imp ph (.imp (synWbr (synC0c) F X) (.classEq X I))) :=
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
  have dv_cache_0003 : z ∉ ((synCop (synC0c) X)).fv :=
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
    z ∉ ((synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)).fv :=
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
  have dv_cache_0006 : z ∉ ((synCsn (synCop (synC0c) I))).fv :=
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
  have dv_cache_0007 : w ∉ ((synCproj1 (.cv z))).fv :=
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
  have dv_cache_0008 : w ∉ ((synCplc (synCproj1 (.cv z)) (synC1c))).fv :=
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
  have dv_cache_0009 : w ∉ ((synCvv)).fv :=
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
  have p0000 := (Nominal.biimpRefl (synWbr (synC0c) F X))
  have p0001 := @gSnex (synCop (synC0c) I)
  have p0002 := @gCsucex w
  have p0003 :=
    @gPprodexg (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G (synCvv) V
  have p0004 :=
    @gSylancr ph
      (.classMem (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv))
      (.classMem G V)
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      p0002 hyp_fnfreclem2_2 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec w G I
      dv_cache_0001 dv_cache_0002
  have p0006 :=
    @gEqtri F (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G))
      hyp_fnfreclem2_1 p0005
  have p0007 :=
    @gClos1basesucg z (synCop (synC0c) X) F
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0006
  have p0008 :=
    @gSylancr ph (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      (synWb (.classMem (synCop (synC0c) X) F)
        (synWo (.classMem (synCop (synC0c) X) (synCsn (synCop (synC0c) I))) (synWrex z F
            (synWbr (.cv z) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
              (synCop (synC0c) X)))))
      p0001 p0004 p0007
  have p0009 := @gN0cex
  have p0010 := @gOpexg (synC0c) I (synCvv) (synCdm G)
  have p0011 :=
    @gSylancr ph (.classMem (synC0c) (synCvv)) (.classMem I (synCdm G))
      (.classMem (synCop (synC0c) I) (synCvv)) p0009 hyp_fnfreclem2_3 p0010
  have p0012 := @gElsnc2g (synCop (synC0c) X) (synCop (synC0c) I) (synCvv)
  have p0013 :=
    @gSyl ph (.classMem (synCop (synC0c) I) (synCvv))
      (synWb (.classMem (synCop (synC0c) X) (synCsn (synCop (synC0c) I)))
        (.classEq (synCop (synC0c) X) (synCop (synC0c) I)))
      p0011 p0012
  have p0014 := @gOpth (synC0c) X (synC0c) I
  have p0015 :=
    @gSimprbi (.classEq (synCop (synC0c) X) (synCop (synC0c) I))
      (.classEq (synC0c) (synC0c)) (.classEq X I) p0014
  have p0016 :=
    @gSyl6bi ph (.classMem (synCop (synC0c) X) (synCsn (synCop (synC0c) I)))
      (.classEq (synCop (synC0c) X) (synCop (synC0c) I)) (.classEq X I) p0013 p0015
  have p0017 := @gN0cnsuc (synCproj1 (.cv z))
  have p0018 :=
    (Nominal.biimpRefl (synWne (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c)))
  have p0019 :=
    @gMpbi (synWne (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))
      (.neg (.classEq (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))) p0017 p0018
  have p0020 :=
    @gIntnanr (.classEq (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))
      (synWbr (synCproj2 (.cv z)) G X) p0019
  have p0021 :=
    @gQrpprod (synCproj1 (.cv z)) (synCproj2 (.cv z)) (synC0c) X
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G
  have p0022 := @gOpeq (.cv z)
  have p0023 :=
    @gBreq1i (.cv z) (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z)))
      (synCop (synC0c) X)
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) p0022
  have p0024 := @gVex z
  have p0025 := @gProj1ex (.cv z) p0024
  have p0026 := @gAddceq1 (.cv w) (synCproj1 (.cv z)) (synC1c)
  have p0027 := @gEqid (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
  have p0028 := @gN1cex
  have p0029 := @gAddcex (synCproj1 (.cv z)) (synC1c) p0025 p0028
  have p0030 :=
    @gFvmpt w (synCproj1 (.cv z)) (synCplc (.cv w) (synC1c))
      (synCplc (synCproj1 (.cv z)) (synC1c)) (synCvv)
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0026 p0027 p0029
  have p0031 := Nominal.mp p0025 p0030
  have p0032 :=
    @gEqeq1i
      (synCfv (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCproj1 (.cv z)))
      (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c) p0031
  have p0033 := @gVex w
  have p0035 := @gAddcex (.cv w) (synC1c) p0033 p0028
  have p0036 :=
    @gFnmpti w (synCvv) (synCplc (.cv w) (synC1c))
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) dv_cache_0009 p0035 p0027
  have p0037 :=
    @gFnbrfvb (synCvv) (synCproj1 (.cv z)) (synC0c)
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
  have p0038 :=
    @gMp2an (synWfn (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv))
      (.classMem (synCproj1 (.cv z)) (synCvv))
      (synWb (.classEq (synCfv (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
            (synCproj1 (.cv z))) (synC0c))
        (synWbr (synCproj1 (.cv z)) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synC0c)))
      p0036 p0025 p0037
  have p0039 :=
    @gBitr3i (.classEq (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))
      (.classEq
        (synCfv (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCproj1 (.cv z)))
        (synC0c))
      (synWbr (synCproj1 (.cv z)) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
        (synC0c))
      p0032 p0038
  have p0040 :=
    @gAnbi1i (.classEq (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))
      (synWbr (synCproj1 (.cv z)) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
        (synC0c))
      (synWbr (synCproj2 (.cv z)) G X) p0039
  have p0041 :=
    @gN3bitr4i
      (synWbr (synCop (synCproj1 (.cv z)) (synCproj2 (.cv z)))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synC0c) X))
      (synWa (synWbr (synCproj1 (.cv z)) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synC0c)) (synWbr (synCproj2 (.cv z)) G X))
      (synWbr (.cv z) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synC0c) X))
      (synWa (.classEq (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))
        (synWbr (synCproj2 (.cv z)) G X))
      p0021 p0023 p0040
  have p0042 :=
    @gMtbir
      (synWbr (.cv z) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synC0c) X))
      (synWa (.classEq (synCplc (synCproj1 (.cv z)) (synC1c)) (synC0c))
        (synWbr (synCproj2 (.cv z)) G X))
      p0020 p0041
  have p0043 :=
    @gA1i
      (.neg (synWbr (.cv z) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synC0c) X)))
      (.classMem (.cv z) F) p0042
  have p0044 :=
    @gNrex
      (synWbr (.cv z) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synC0c) X))
      z F p0043
  have p0045 :=
    @gPm221i
      (synWrex z F (synWbr (.cv z)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synC0c) X)))
      (.classEq X I) p0044
  have p0046 :=
    @gA1i
      (.imp (synWrex z F (synWbr (.cv z)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synC0c) X))) (.classEq X I))
      ph p0045
  have p0047 :=
    @gJaod ph (.classMem (synCop (synC0c) X) (synCsn (synCop (synC0c) I)))
      (.classEq X I)
      (synWrex z F (synWbr (.cv z)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synC0c) X)))
      p0016 p0046
  have p0048 :=
    @gSylbid ph (.classMem (synCop (synC0c) X) F)
      (synWo (.classMem (synCop (synC0c) X) (synCsn (synCop (synC0c) I))) (synWrex z F
          (synWbr (.cv z) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synC0c) X))))
      (.classEq X I) p0008 p0047
  have p0049 :=
    @gSyl5bi (synWbr (synC0c) F X) (.classMem (synCop (synC0c) X) F) ph
      (.classEq X I) p0000 p0048
  exact p0049

/-- Checked nominal proof certificate identified upstream as `g_fnfreclem3`. -/
@[expose]
noncomputable def gFnfreclem3 (ph : Wff) (z : Var) (F : Class) (G : Class) (I : Class)
    (V : Class) (X : Class) (Y : Class) (dv_F_z : z ∉ F.fv) (dv_G_z : z ∉ G.fv)
    (_dv_I_z : z ∉ I.fv) (dv_X_z : z ∉ X.fv) (dv_Y_z : z ∉ Y.fv) (dv_ph_z : z ∉ ph.fv)
    (hyp_fnfreclem2_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_fnfreclem2_2 : Nominal.NPrf (.imp ph (.classMem G V)))
    (hyp_fnfreclem2_3 : Nominal.NPrf (.imp ph (.classMem I (synCdm G))))
    (hyp_fnfreclem2_4 : Nominal.NPrf (.imp ph (synWss (synCrn G) (synCdm G))))
    (hyp_fnfreclem3_5 : Nominal.NPrf (.imp ph (.classMem X (synCnnc))))
    (hyp_fnfreclem3_6 : Nominal.NPrf (.imp ph (synWbr (synCplc X (synC1c)) F Y))) :
    Nominal.NPrf
      (.imp ph (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)))) :=
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
  have dv_cache_0005 : w ∉ ((synCplc (.cv t) (synC1c))).fv :=
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
  have dv_cache_0006 : w ∉ ((synCvv)).fv :=
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
  have dv_cache_0007 : t ∉ ((synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))).fv :=
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
      ((synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc X (synC1c)) Y)))).fv :=
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
      ((synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc X (synC1c)) Y)))).fv :=
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
    a ∉ ((synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)))).fv :=
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
  have dv_cache_0014 : a ∉ ((synCop (synCplc X (synC1c)) Y)).fv :=
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
    a ∉ ((synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)).fv :=
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
  have dv_cache_0017 : a ∉ ((synCsn (synCop (synC0c) I))).fv :=
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
  have p0000 := @gN0cex
  have p0001 := @gOpexg (synC0c) I (synCvv) (synCdm G)
  have p0002 :=
    @gSylancr ph (.classMem (synC0c) (synCvv)) (.classMem I (synCdm G))
      (.classMem (synCop (synC0c) I) (synCvv)) p0000 hyp_fnfreclem2_3 p0001
  have p0003 :=
    @gElsnc2g (synCop (synCplc X (synC1c)) Y) (synCop (synC0c) I) (synCvv)
  have p0004 :=
    @gSyl ph (.classMem (synCop (synC0c) I) (synCvv))
      (synWb (.classMem (synCop (synCplc X (synC1c)) Y) (synCsn (synCop (synC0c) I)))
        (.classEq (synCop (synCplc X (synC1c)) Y) (synCop (synC0c) I)))
      p0002 p0003
  have p0005 := @gOpth (synCplc X (synC1c)) Y (synC0c) I
  have p0006 :=
    @gSimplbi (.classEq (synCop (synCplc X (synC1c)) Y) (synCop (synC0c) I))
      (.classEq (synCplc X (synC1c)) (synC0c)) (.classEq Y I) p0005
  have p0007 := @gN0cnsuc X
  have p0008 := (Nominal.biimpRefl (synWne (synCplc X (synC1c)) (synC0c)))
  have p0009 :=
    @gMpbi (synWne (synCplc X (synC1c)) (synC0c))
      (.neg (.classEq (synCplc X (synC1c)) (synC0c))) p0007 p0008
  have p0010 :=
    @gPm221i (.classEq (synCplc X (synC1c)) (synC0c))
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))) p0009
  have p0011 :=
    @gA1i
      (.imp (.classEq (synCplc X (synC1c)) (synC0c))
        (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))))
      ph p0010
  have p0012 :=
    @gSyl5 (.classEq (synCop (synCplc X (synC1c)) Y) (synCop (synC0c) I))
      (.classEq (synCplc X (synC1c)) (synC0c)) ph
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))) p0006 p0011
  have p0013 :=
    @gSylbid ph
      (.classMem (synCop (synCplc X (synC1c)) Y) (synCsn (synCop (synC0c) I)))
      (.classEq (synCop (synCplc X (synC1c)) Y) (synCop (synC0c) I))
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))) p0004 p0012
  have p0014 := @gVex a
  have p0015 := @gOpeqex t z (.cv a) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0016 := Nominal.mp p0014 p0015
  have p0017 := @gExcom (.classEq (.cv a) (synCop (.cv t) (.cv z))) t z
  have p0018 :=
    @gMpbi (synWex t (synWex z (.classEq (.cv a) (synCop (.cv t) (.cv z)))))
      (synWex z (synWex t (.classEq (.cv a) (synCop (.cv t) (.cv z))))) p0016 p0017
  have p0019 := @gEleq1 (.cv a) (synCop (.cv t) (.cv z)) F
  have p0020 := (Nominal.biimpRefl (synWbr (.cv t) F (.cv z)))
  have p0021 :=
    @gSyl6bbr (.classEq (.cv a) (synCop (.cv t) (.cv z))) (.classMem (.cv a) F)
      (.classMem (synCop (.cv t) (.cv z)) F) (synWbr (.cv t) F (.cv z)) p0019 p0020
  have p0022 :=
    @gAnbi2d (.classEq (.cv a) (synCop (.cv t) (.cv z))) (.classMem (.cv a) F)
      (synWbr (.cv t) F (.cv z)) ph p0021
  have p0023 :=
    @gBreq1 (.cv a) (synCop (.cv t) (.cv z)) (synCop (synCplc X (synC1c)) Y)
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
  have p0024 :=
    @gQrpprod (.cv t) (.cv z) (synCplc X (synC1c)) Y
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G
  have p0025 := @gVex t
  have p0026 := @gAddceq1 (.cv w) (.cv t) (synC1c)
  have p0027 := @gEqid (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
  have p0028 := @gN1cex
  have p0029 := @gAddcex (.cv t) (synC1c) p0025 p0028
  have p0030 :=
    @gFvmpt w (.cv t) (synCplc (.cv w) (synC1c)) (synCplc (.cv t) (synC1c)) (synCvv)
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0026 p0027 p0029
  have p0031 := Nominal.mp p0025 p0030
  have p0032 :=
    @gEqeq1i (synCfv (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (.cv t))
      (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)) p0031
  have p0033 :=
    @gFnmpt w (synCvv) (synCplc (.cv w) (synC1c))
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv) dv_cache_0006 p0027
  have p0035 := @gAddcexg (.cv w) (synC1c) (synCvv) (synCvv)
  have p0036 :=
    @gMpan2 (.classMem (.cv w) (synCvv)) (.classMem (synC1c) (synCvv))
      (.classMem (synCplc (.cv w) (synC1c)) (synCvv)) p0028 p0035
  have p0037 :=
    @gMprg (.classMem (synCplc (.cv w) (synC1c)) (synCvv))
      (synWfn (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv)) w (synCvv)
      p0033 p0036
  have p0038 :=
    @gFnbrfvb (synCvv) (.cv t) (synCplc X (synC1c))
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
  have p0039 :=
    @gMp2an (synWfn (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv))
      (.classMem (.cv t) (synCvv))
      (synWb (.classEq (synCfv (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (.cv t))
          (synCplc X (synC1c)))
        (synWbr (.cv t) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synCplc X (synC1c))))
      p0037 p0025 p0038
  have p0040 :=
    @gBitr3i (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
      (.classEq (synCfv (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (.cv t))
        (synCplc X (synC1c)))
      (synWbr (.cv t) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
        (synCplc X (synC1c)))
      p0032 p0039
  have p0041 :=
    @gAnbi1i (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
      (synWbr (.cv t) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
        (synCplc X (synC1c)))
      (synWbr (.cv z) G Y) p0040
  have p0042 :=
    @gBitr4i
      (synWbr (synCop (.cv t) (.cv z))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) Y))
      (synWa (synWbr (.cv t) (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synCplc X (synC1c))) (synWbr (.cv z) G Y))
      (synWa (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
        (synWbr (.cv z) G Y))
      p0024 p0041
  have p0043 :=
    @gSyl6bb (.classEq (.cv a) (synCop (.cv t) (.cv z)))
      (synWbr (.cv a) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) Y))
      (synWbr (synCop (.cv t) (.cv z))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) Y))
      (synWa (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
        (synWbr (.cv z) G Y))
      p0023 p0042
  have p0044 :=
    @gAnbi12d (.classEq (.cv a) (synCop (.cv t) (.cv z)))
      (synWa ph (.classMem (.cv a) F)) (synWa ph (synWbr (.cv t) F (.cv z)))
      (synWbr (.cv a) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) Y))
      (synWa (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
        (synWbr (.cv z) G Y))
      p0022 p0043
  have p0045 := @gBreldm (.cv t) (.cv z) F
  have p0046 :=
    @gAdantl (synWbr (.cv t) F (.cv z)) (.classMem (.cv t) (synCdm F)) ph p0045
  have p0047 :=
    @gDmfrec ph F G I V hyp_fnfreclem2_1 hyp_fnfreclem2_2 hyp_fnfreclem2_3
      hyp_fnfreclem2_4
  have p0048 :=
    @gAdantr ph (.classEq (synCdm F) (synCnnc)) (synWbr (.cv t) F (.cv z)) p0047
  have p0049 :=
    @gEleqtrd (synWa ph (synWbr (.cv t) F (.cv z))) (.cv t) (synCdm F) (synCnnc)
      p0046 p0048
  have p0050 :=
    @gAdantr ph (.classMem X (synCnnc)) (synWbr (.cv t) F (.cv z)) hyp_fnfreclem3_5
  have p0051 := @gPeano4 (.cv t) X
  have p0052 :=
    @gN3expia (.classMem (.cv t) (synCnnc)) (.classMem X (synCnnc))
      (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c))) (.classEq (.cv t) X)
      p0051
  have p0053 :=
    @gSyl2anc (synWa ph (synWbr (.cv t) F (.cv z))) (.classMem (.cv t) (synCnnc))
      (.classMem X (synCnnc))
      (.imp (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c))) (.classEq (.cv t) X))
      p0049 p0050 p0052
  have p0054 := @gBreq1 (.cv t) X (.cv z) F
  have p0055 :=
    @gBiimpcd (.classEq (.cv t) X) (synWbr (.cv t) F (.cv z)) (synWbr X F (.cv z))
      p0054
  have p0056 :=
    @gAdantl (synWbr (.cv t) F (.cv z))
      (.imp (.classEq (.cv t) X) (synWbr X F (.cv z))) ph p0055
  have p0057 :=
    @gSyld (synWa ph (synWbr (.cv t) F (.cv z)))
      (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c))) (.classEq (.cv t) X)
      (synWbr X F (.cv z)) p0053 p0056
  have p0058 :=
    @gAnim1d (synWa ph (synWbr (.cv t) F (.cv z)))
      (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c))) (synWbr X F (.cv z))
      (synWbr (.cv z) G Y) p0057
  have p0059 :=
    @gImp (synWa ph (synWbr (.cv t) F (.cv z)))
      (synWa (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
        (synWbr (.cv z) G Y))
      (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)) p0058
  have p0060 :=
    @gSyl6bi (.classEq (.cv a) (synCop (.cv t) (.cv z)))
      (synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) Y)))
      (synWa (synWa ph (synWbr (.cv t) F (.cv z)))
        (synWa (.classEq (synCplc (.cv t) (synC1c)) (synCplc X (synC1c)))
          (synWbr (.cv z) G Y)))
      (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)) p0044 p0059
  have p0061 :=
    @gCom12 (.classEq (.cv a) (synCop (.cv t) (.cv z)))
      (synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) Y)))
      (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)) p0060
  have p0062 :=
    @gExlimdv
      (synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) Y)))
      (.classEq (.cv a) (synCop (.cv t) (.cv z)))
      (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)) t dv_cache_0007 dv_cache_0008
      p0061
  have p0063 :=
    @gEximdv
      (synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) Y)))
      (synWex t (.classEq (.cv a) (synCop (.cv t) (.cv z))))
      (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)) z dv_cache_0009 p0062
  have p0064 :=
    @gMpi
      (synWa (synWa ph (.classMem (.cv a) F)) (synWbr (.cv a)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) Y)))
      (synWex z (synWex t (.classEq (.cv a) (synCop (.cv t) (.cv z)))))
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))) p0018 p0063
  have p0065 :=
    @gEx (synWa ph (.classMem (.cv a) F))
      (synWbr (.cv a) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) Y))
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))) p0064
  have p0066 :=
    @gRexlimdva ph
      (synWbr (.cv a) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) Y))
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y))) a F dv_cache_0010
      dv_cache_0011 p0065
  have p0067 := (Nominal.biimpRefl (synWbr (synCplc X (synC1c)) F Y))
  have p0068 := @gSnex (synCop (synC0c) I)
  have p0069 := @gCsucex w
  have p0070 :=
    @gPprodexg (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G (synCvv) V
  have p0071 :=
    @gSylancr ph
      (.classMem (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv))
      (.classMem G V)
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      p0069 hyp_fnfreclem2_2 p0070
  have p0072 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec w G I
      dv_cache_0012 dv_cache_0013
  have p0073 :=
    @gEqtri F (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G))
      hyp_fnfreclem2_1 p0072
  have p0074 :=
    @gClos1basesucg a (synCop (synCplc X (synC1c)) Y) F
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv) dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 p0073
  have p0075 :=
    @gSylancr ph (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      (synWb (.classMem (synCop (synCplc X (synC1c)) Y) F) (synWo
          (.classMem (synCop (synCplc X (synC1c)) Y) (synCsn (synCop (synC0c) I)))
          (synWrex a F (synWbr (.cv a)
              (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
              (synCop (synCplc X (synC1c)) Y)))))
      p0068 p0071 p0074
  have p0076 :=
    @gSyl5bb (synWbr (synCplc X (synC1c)) F Y)
      (.classMem (synCop (synCplc X (synC1c)) Y) F) ph
      (synWo (.classMem (synCop (synCplc X (synC1c)) Y) (synCsn (synCop (synC0c) I)))
        (synWrex a F (synWbr (.cv a)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc X (synC1c)) Y))))
      p0067 p0075
  have p0077 :=
    @gMpbid ph (synWbr (synCplc X (synC1c)) F Y)
      (synWo (.classMem (synCop (synCplc X (synC1c)) Y) (synCsn (synCop (synC0c) I)))
        (synWrex a F (synWbr (.cv a)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc X (synC1c)) Y))))
      hyp_fnfreclem3_6 p0076
  have p0078 :=
    @gMpjaod ph
      (.classMem (synCop (synCplc X (synC1c)) Y) (synCsn (synCop (synC0c) I)))
      (synWex z (synWa (synWbr X F (.cv z)) (synWbr (.cv z) G Y)))
      (synWrex a F (synWbr (.cv a)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) Y)))
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

/-- Checked nominal proof certificate identified upstream as `g_fnfrec`. -/
@[expose]
noncomputable def gFnfrec (ph : Wff) (F : Class) (G : Class) (I : Class)
    (hyp_fnfrec_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_fnfrec_2 : Nominal.NPrf (.imp ph (.classMem G (synCfuns))))
    (hyp_fnfrec_3 : Nominal.NPrf (.imp ph (.classMem I (synCdm G))))
    (hyp_fnfrec_4 : Nominal.NPrf (.imp ph (synWss (synCrn G) (synCdm G)))) :
    Nominal.NPrf (.imp ph (synWfn F (synCnnc))) :=
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
  have dv_cache_0007 : y ∉ ((Wff.classEq (.cv w) (synC0c))).fv :=
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
  have dv_cache_0008 : z ∉ ((Wff.classEq (.cv w) (synC0c))).fv :=
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
  have dv_cache_0011 : y ∉ ((Wff.classEq (.cv w) (synCplc (.cv t) (synC1c)))).fv :=
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
  have dv_cache_0012 : z ∉ ((Wff.classEq (.cv w) (synCplc (.cv t) (synC1c)))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
            (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))) (.objEq y z))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
            (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))) (.objEq y z))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
            (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))).fv :=
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
      ((Wff.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
            (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))).fv :=
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
      ((synWa (synWa ph (.classMem (.cv t) (synCnnc)))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)))).fv :=
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
      ((synWa (synWa ph (.classMem (.cv t) (synCnnc)))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)))).fv :=
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
    z ∉ ((synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))).fv :=
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
    y ∉ ((synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))).fv :=
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
      ((synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
                (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
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
      ((synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
                (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
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
      ((Wff.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
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
      ((Wff.all y (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
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
            (.imp (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z)))
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
      ((Wff.all y (.all z (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
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
      ((Wff.all a (.all b (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
                (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))))).fv :=
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
  have p0000 := @gBreldm (.cv x) (.cv y) F
  have p0001 :=
    @gAdantl (synWbr (.cv x) F (.cv y)) (.classMem (.cv x) (synCdm F)) ph p0000
  have p0002 :=
    @gDmfrec ph F G I (synCfuns) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3 hyp_fnfrec_4
  have p0003 :=
    @gAdantr ph (.classEq (synCdm F) (synCnnc)) (synWbr (.cv x) F (.cv y)) p0002
  have p0004 :=
    @gEleqtrd (synWa ph (synWbr (.cv x) F (.cv y))) (.cv x) (synCdm F) (synCnnc)
      p0001 p0003
  have p0005 :=
    @gAdantrr ph (synWbr (.cv x) F (.cv y)) (.classMem (.cv x) (synCnnc))
      (synWbr (.cv x) F (.cv z)) p0004
  have p0006 := @gFrecexg F G I (synCfuns) hyp_fnfrec_1
  have p0007 :=
    @gFnfreclem1 y z w F (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @gN3syl ph (.classMem G (synCfuns)) (.classMem F (synCvv))
      (.classMem (.cab w (.all y (.all z
              (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
                (.objEq y z))))) (synCvv))
      hyp_fnfrec_2 p0006 p0007
  have p0009 := @gBreq1 (.cv w) (synC0c) (.cv y) F
  have p0010 := @gBreq1 (.cv w) (synC0c) (.cv z) F
  have p0011 :=
    @gAnbi12d (.classEq (.cv w) (synC0c)) (synWbr (.cv w) F (.cv y))
      (synWbr (synC0c) F (.cv y)) (synWbr (.cv w) F (.cv z))
      (synWbr (synC0c) F (.cv z)) p0009 p0010
  have p0012 :=
    @gImbi1d (.classEq (.cv w) (synC0c))
      (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
      (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z))) (.objEq y z)
      p0011
  have p0013 :=
    @gN2albidv (.classEq (.cv w) (synC0c))
      (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z))) (.objEq y z))
      y z dv_cache_0007 dv_cache_0008 p0012
  have p0014 := @gBreq1 (.cv w) (.cv t) (.cv y) F
  have p0015 := @gBreq1 (.cv w) (.cv t) (.cv z) F
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w t) (synWb (synWbr (.cv w) F (.cv y)) (synWbr (.cv t) F (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w t) (synWb (synWbr (.cv w) F (.cv z)) (synWbr (.cv t) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gAnbi12d (.objEq w t) (synWbr (.cv w) F (.cv y)) (synWbr (.cv t) F (.cv y))
      (synWbr (.cv w) F (.cv z)) (synWbr (.cv t) F (.cv z)) p0016_e00_recanon
      p0016_e01_recanon
  have p0017 :=
    @gImbi1d (.objEq w t)
      (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
      (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z) p0016
  have p0018 :=
    @gN2albidv (.objEq w t)
      (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
      y z dv_cache_0009 dv_cache_0010 p0017
  have p0019 := @gBreq1 (.cv w) (synCplc (.cv t) (synC1c)) (.cv y) F
  have p0020 := @gBreq1 (.cv w) (synCplc (.cv t) (synC1c)) (.cv z) F
  have p0021 :=
    @gAnbi12d (.classEq (.cv w) (synCplc (.cv t) (synC1c))) (synWbr (.cv w) F (.cv y))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv y)) (synWbr (.cv w) F (.cv z))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv z)) p0019 p0020
  have p0022 :=
    @gImbi1d (.classEq (.cv w) (synCplc (.cv t) (synC1c)))
      (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
      (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv z)))
      (.objEq y z) p0021
  have p0023 :=
    @gN2albidv (.classEq (.cv w) (synCplc (.cv t) (synC1c)))
      (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))) (.objEq y z))
      y z dv_cache_0011 dv_cache_0012 p0022
  have p0024 := @gBreq2 (.cv y) (.cv a) (synCplc (.cv t) (synC1c)) F
  have p0025 := @gBreq2 (.cv z) (.cv b) (synCplc (.cv t) (synC1c)) F
  have p0026_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y a) (synWb (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0026_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq z b) (synWb (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @gBi2anan9 (.objEq y a) (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)) (.objEq z b)
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)) p0026_e00_recanon p0026_e01_recanon
  have p0027 := @gEqeq12 (.cv y) (.cv a) (.cv z) (.cv b)
  have p0028_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq y a) (.objEq z b)) (synWb (.objEq y z) (.objEq a b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
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
    @gImbi12d (synWa (.objEq y a) (.objEq z b))
      (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv z)))
      (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)))
      (.objEq y z) (.objEq a b) p0026 p0028_e01_recanon
  have p0029 :=
    @gCbval2v
      (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))
      y z a b dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0006 dv_cache_0019 p0028
  have p0030 :=
    @gSyl6bb (.classEq (.cv w) (synCplc (.cv t) (synC1c)))
      (.all y (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.objEq y z))))
      (.all y (.all z (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv y))
              (synWbr (synCplc (.cv t) (synC1c)) F (.cv z))) (.objEq y z))))
      (.all a (.all b (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
              (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))))
      p0023 p0029
  have p0031 := @gBreq1 (.cv w) (.cv x) (.cv y) F
  have p0032 := @gBreq1 (.cv w) (.cv x) (.cv z) F
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (synWb (synWbr (.cv w) F (.cv y)) (synWbr (.cv x) F (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0033_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (synWb (synWbr (.cv w) F (.cv z)) (synWbr (.cv x) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @gAnbi12d (.objEq w x) (synWbr (.cv w) F (.cv y)) (synWbr (.cv x) F (.cv y))
      (synWbr (.cv w) F (.cv z)) (synWbr (.cv x) F (.cv z)) p0033_e00_recanon
      p0033_e01_recanon
  have p0034 :=
    @gImbi1d (.objEq w x)
      (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
      (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z) p0033
  have p0035 :=
    @gN2albidv (.objEq w x)
      (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z))
      y z dv_cache_0020 dv_cache_0021 p0034
  have p0036 :=
    @gFnfreclem2 ph F G I (synCfuns) (.cv y) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3
      hyp_fnfrec_4
  have p0037 := @gImp ph (synWbr (synC0c) F (.cv y)) (.classEq (.cv y) I) p0036
  have p0038 :=
    @gAdantrr ph (synWbr (synC0c) F (.cv y)) (.classEq (.cv y) I)
      (synWbr (synC0c) F (.cv z)) p0037
  have p0039 :=
    @gFnfreclem2 ph F G I (synCfuns) (.cv z) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3
      hyp_fnfrec_4
  have p0040 := @gImp ph (synWbr (synC0c) F (.cv z)) (.classEq (.cv z) I) p0039
  have p0041 :=
    @gAdantrl ph (synWbr (synC0c) F (.cv z)) (.classEq (.cv z) I)
      (synWbr (synC0c) F (.cv y)) p0040
  have p0042 :=
    @gEqtr4d
      (synWa ph (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z))))
      (.cv y) I (.cv z) p0038 p0041
  have p0043_e00_recanon :
    Nominal.NPrf
      (.imp (synWa ph (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z))))
        (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0042
  have p0043 :=
    @gEx ph (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z)))
      (.objEq y z) p0043_e00_recanon
  have p0044 :=
    @gAlrimivv ph
      (.imp (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z))) (.objEq y z))
      y z dv_cache_0022 dv_cache_0023 p0043
  have p0045 :=
    @gAd2antrr ph (.classMem G (synCfuns)) (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)) hyp_fnfrec_2
  have p0046 :=
    @gAd2antrr ph (.classMem I (synCdm G)) (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)) hyp_fnfrec_3
  have p0047 :=
    @gAd2antrr ph (synWss (synCrn G) (synCdm G)) (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)) hyp_fnfrec_4
  have p0048 :=
    @gSimplr ph (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
  have p0049 :=
    @gSimpr (synWa ph (.classMem (.cv t) (synCnnc)))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
  have p0050 :=
    @gFnfreclem3
      (synWa (synWa ph (.classMem (.cv t) (synCnnc)))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv a)))
      y F G I (synCfuns) (.cv t) (.cv a) dv_cache_0002 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0028 hyp_fnfrec_1 p0045 p0046 p0047 p0048 p0049
  have p0051 :=
    @gAdantlrr ph (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
      (synWex y (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a))))
      (.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))))
      p0050
  have p0052 :=
    @gEx
      (synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
      (synWex y (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))) p0051
  have p0053 :=
    @gAd2antrr ph (.classMem G (synCfuns)) (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)) hyp_fnfrec_2
  have p0054 :=
    @gAd2antrr ph (.classMem I (synCdm G)) (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)) hyp_fnfrec_3
  have p0055 :=
    @gAd2antrr ph (synWss (synCrn G) (synCdm G)) (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)) hyp_fnfrec_4
  have p0056 :=
    @gSimplr ph (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))
  have p0057 :=
    @gSimpr (synWa ph (.classMem (.cv t) (synCnnc)))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))
  have p0058 :=
    @gFnfreclem3
      (synWa (synWa ph (.classMem (.cv t) (synCnnc)))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)))
      z F G I (synCfuns) (.cv t) (.cv b) dv_cache_0003 dv_cache_0029 dv_cache_0030
      dv_cache_0031 dv_cache_0032 dv_cache_0033 hyp_fnfrec_1 p0053 p0054 p0055 p0056 p0057
  have p0059 :=
    @gAdantlrr ph (.classMem (.cv t) (synCnnc))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))
      (synWex z (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))
      (.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))))
      p0058
  have p0060 :=
    @gEx
      (synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))
      (synWex z (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))) p0059
  have p0061 :=
    @gAnim12d
      (synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
      (synWex y (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a))))
      (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))
      (synWex z (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))) p0052
      p0060
  have p0062 :=
    @gEeanv (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
      (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))) y z dv_cache_0034
      dv_cache_0035
  have p0063 :=
    @gSyl6ibr
      (synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)))
      (synWa (synWex y (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a))))
        (synWex z (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
            (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))))
      p0061 p0062
  have p0064 :=
    @gN1929
      (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
          (.objEq y z)))
      (synWex z (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
          (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))
      y
  have p0065 :=
    @gN1929
      (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
      (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
        (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))
      z
  have p0066 :=
    @gEximi
      (synWa (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))) (synWex z
          (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
            (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))))
      (synWex z (synWa (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))
          (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
            (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))))
      y p0065
  have p0067 :=
    @gSyl
      (synWa (.all y (.all z
            (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
              (.objEq y z)))) (synWex y (synWex z
            (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
              (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))))
      (synWex y (synWa (.all z
            (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
              (.objEq y z))) (synWex z
            (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
              (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))))
      (synWex y (synWex z (synWa
            (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
            (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
              (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))))
      p0064 p0066
  have p0068 :=
    @gPm335 (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
      (.objEq y z)
  have p0069 := @gBreq1 (.cv y) (.cv z) (.cv a) G
  have p0070_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0069
  have p0070 :=
    @gAnbi1d (.objEq y z) (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv a))
      (synWbr (.cv z) G (.cv b)) p0070_e00_recanon
  have p0071 :=
    @gBiimpa (.objEq y z)
      (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b)))
      (synWa (synWbr (.cv z) G (.cv a)) (synWbr (.cv z) G (.cv b))) p0070
  have p0072 := @gElfunsi G
  have p0073 := @gFunbrfv (.cv z) (.cv a) G
  have p0074 :=
    @gN3syl ph (.classMem G (synCfuns)) (synWfun G)
      (.imp (synWbr (.cv z) G (.cv a)) (.classEq (synCfv G (.cv z)) (.cv a)))
      hyp_fnfrec_2 p0072 p0073
  have p0075 := @gFunbrfv (.cv z) (.cv b) G
  have p0076 :=
    @gN3syl ph (.classMem G (synCfuns)) (synWfun G)
      (.imp (synWbr (.cv z) G (.cv b)) (.classEq (synCfv G (.cv z)) (.cv b)))
      hyp_fnfrec_2 p0072 p0075
  have p0077 :=
    @gAnim12d ph (synWbr (.cv z) G (.cv a)) (.classEq (synCfv G (.cv z)) (.cv a))
      (synWbr (.cv z) G (.cv b)) (.classEq (synCfv G (.cv z)) (.cv b)) p0074 p0076
  have p0078 := @gEqtr2 (synCfv G (.cv z)) (.cv a) (.cv b)
  have p0079_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (synCfv G (.cv z)) (.cv a))
          (.classEq (synCfv G (.cv z)) (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCfv synCio synCuni synWex synCsn synWbr synCop synCun
          synCnin synWnan synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0078
  have p0079 :=
    @gSyl56
      (synWa (.objEq y z) (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))))
      (synWa (synWbr (.cv z) G (.cv a)) (synWbr (.cv z) G (.cv b))) ph
      (synWa (.classEq (synCfv G (.cv z)) (.cv a)) (.classEq (synCfv G (.cv z)) (.cv b)))
      (.objEq a b) p0071 p0077 p0079_e02_recanon
  have p0080 :=
    @gExp3a ph (.objEq y z)
      (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))) (.objEq a b) p0079
  have p0081 :=
    @gSyl5
      (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
        (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z)))
      (.objEq y z) ph
      (.imp (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))) (.objEq a b))
      p0068 p0080
  have p0082 :=
    @gExp3a ph (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
      (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))) (.objEq a b))
      p0081
  have p0083 :=
    @gCom34 ph (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
      (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
      (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))) (.objEq a b) p0082
  have p0084 :=
    @gImp3a ph (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
      (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b)))
      (.imp (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
        (.objEq a b))
      p0083
  have p0085 :=
    @gCom12 ph
      (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
        (synWa (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))))
      (.imp (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
        (.objEq a b))
      p0084
  have p0086 :=
    @gAn4s (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))
      (synWbr (.cv y) G (.cv a)) (synWbr (.cv z) G (.cv b))
      (.imp ph (.imp (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z)) (.objEq a b)))
      p0085
  have p0087 :=
    @gCom3l
      (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
        (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))
      ph
      (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
      (.objEq a b) p0086
  have p0088 :=
    @gImp3a ph
      (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
      (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
        (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))
      (.objEq a b) p0087
  have p0089 :=
    @gExlimdvv ph
      (synWa (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
          (.objEq y z)) (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
          (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))
      (.objEq a b) y z dv_cache_0036 dv_cache_0037 dv_cache_0022 dv_cache_0023 p0088
  have p0090 :=
    @gAdantr ph
      (.imp (synWex y (synWex z (synWa
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))
              (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
                (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))))
        (.objEq a b))
      (.classMem (.cv t) (synCnnc)) p0089
  have p0091 :=
    @gSyl5
      (synWa (.all y (.all z
            (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
              (.objEq y z)))) (synWex y (synWex z
            (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
              (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))))
      (synWex y (synWex z (synWa
            (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z))) (.objEq y z))
            (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
              (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))))
      (synWa ph (.classMem (.cv t) (synCnnc))) (.objEq a b) p0067 p0090
  have p0092 :=
    @gExp3a (synWa ph (.classMem (.cv t) (synCnnc)))
      (.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
            (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))))
      (.objEq a b) p0091
  have p0093 :=
    @gImpr ph (.classMem (.cv t) (synCnnc))
      (.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (.imp (synWex y (synWex z
            (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
              (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b)))))) (.objEq a b))
      p0092
  have p0094 :=
    @gSyld
      (synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
        (synWbr (synCplc (.cv t) (synC1c)) F (.cv b)))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv y) G (.cv a)))
            (synWa (synWbr (.cv t) F (.cv z)) (synWbr (.cv z) G (.cv b))))))
      (.objEq a b) p0063 p0093
  have p0095 :=
    @gAlrimivv
      (synWa ph (synWa (.classMem (.cv t) (synCnnc)) (.all y (.all z
              (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
                (.objEq y z))))))
      (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
          (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))
      a b dv_cache_0038 dv_cache_0039 p0094
  have p0096 :=
    @gExpr ph (.classMem (.cv t) (synCnnc))
      (.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (.all a (.all b (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
              (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))))
      p0095
  have p0097 :=
    @gAncoms ph (.classMem (.cv t) (synCnnc))
      (.imp (.all y (.all z
            (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
              (.objEq y z)))) (.all a (.all b (.imp
              (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
                (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b)))))
      p0096
  have p0098_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv x)) (synWb (.all y (.all z
              (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
                (.objEq y z)))) (.all y (.all z
              (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
                (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0098 :=
    @gFindsd
      (.all y (.all z (.imp (synWa (synWbr (.cv w) F (.cv y)) (synWbr (.cv w) F (.cv z)))
            (.objEq y z))))
      (.all y (.all z (.imp (synWa (synWbr (synC0c) F (.cv y)) (synWbr (synC0c) F (.cv z)))
            (.objEq y z))))
      (.all y (.all z (.imp (synWa (synWbr (.cv t) F (.cv y)) (synWbr (.cv t) F (.cv z)))
            (.objEq y z))))
      (.all a (.all b (.imp (synWa (synWbr (synCplc (.cv t) (synC1c)) F (.cv a))
              (synWbr (synCplc (.cv t) (synC1c)) F (.cv b))) (.objEq a b))))
      (.all y (.all z (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
            (.objEq y z))))
      ph w t (.cv x) (synCvv) dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
      dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 p0008 p0013 p0018 p0030
      p0098_e04_recanon p0044 p0097
  have p0099 :=
    @gN1921bbi (synWa (.classMem (.cv x) (synCnnc)) ph)
      (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z))
      y z p0098
  have p0100 :=
    @gEx (.classMem (.cv x) (synCnnc)) ph
      (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z))
      p0099
  have p0101 :=
    @gImp3a (.classMem (.cv x) (synCnnc)) ph
      (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z) p0100
  have p0102 :=
    @gMpcom (.classMem (.cv x) (synCnnc))
      (synWa ph (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))))
      (.objEq y z) p0005 p0101
  have p0103 :=
    @gEx ph (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z)
      p0102
  have p0104 :=
    @gAlrimivv ph
      (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z))) (.objEq y z))
      y z dv_cache_0022 dv_cache_0023 p0103
  have p0105 :=
    @gAlrimiv ph
      (.all y (.all z (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
            (.objEq y z))))
      x dv_cache_0048 p0104
  have p0106 :=
    @gDffun2 x y z F dv_cache_0049 dv_cache_0002 dv_cache_0003 dv_cache_0050
      dv_cache_0051 dv_cache_0006
  have p0107 :=
    @gSylibr ph
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))
              (.objEq y z)))))
      (synWfun F) p0105 p0106
  have p0108 := (Nominal.biimpRefl (synWfn F (synCnnc)))
  have p0109 :=
    @gSylanbrc ph (synWfun F) (.classEq (synCdm F) (synCnnc)) (synWfn F (synCnnc))
      p0107 p0002 p0108
  exact p0109


end NFChoice.DirectNominalPrf.WPPReplay

end
