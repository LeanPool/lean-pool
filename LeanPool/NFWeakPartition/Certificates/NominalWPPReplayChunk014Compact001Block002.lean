/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_frec0 (ph : Wff) (F : Class) (G : Class) (I : Class)
    (hyp_frec0_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_frec0_2 : Nominal.NPrf (.imp ph (.classMem G (syn_cfuns))))
    (hyp_frec0_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G))))
    (hyp_frec0_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F (syn_c0c)) I)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
  have dv_cache_0003 : y ∉ ((syn_cop (syn_c0c) I)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_y_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0005 :
    y ∉ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
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
  have dv_cache_0006 : y ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_y_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_peano1
  have p0001 := @g_opexg (syn_c0c) I (syn_cnnc) (syn_cdm G)
  have p0002 :=
    @g_sylancr ph (.classMem (syn_c0c) (syn_cnnc)) (.classMem I (syn_cdm G))
      (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) p0000 hyp_frec0_3 p0001
  have p0003 := @g_snidg (syn_cop (syn_c0c) I) (syn_cvv)
  have p0004 :=
    @g_syl ph (.classMem (syn_cop (syn_c0c) I) (syn_cvv))
      (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) p0002 p0003
  have p0005 :=
    @g_orcd ph (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I)))
      (syn_wrex y F (syn_wbr (.cv y)
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
          (syn_cop (syn_c0c) I)))
      p0004
  have p0006 := @g_snex (syn_cop (syn_c0c) I)
  have p0007 := @g_csucex x
  have p0008 :=
    @g_pprodexg (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G (syn_cvv)
      (syn_cfuns)
  have p0009 :=
    @g_sylancr ph
      (.classMem (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_cvv))
      (.classMem G (syn_cfuns))
      (.classMem (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cvv))
      p0007 hyp_frec0_2 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G I
      dv_cache_0001 dv_cache_0002
  have p0011 :=
    @g_eqtri F (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      hyp_frec0_1 p0010
  have p0012 :=
    @g_clos1basesucg y (syn_cop (syn_c0c) I) F
      (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0011
  have p0013 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_c0c) I) F)
        (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F
            (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
              (syn_cop (syn_c0c) I)))))
      p0006 p0009 p0012
  have p0014 :=
    @g_mpbird ph (.classMem (syn_cop (syn_c0c) I) F)
      (syn_wo (.classMem (syn_cop (syn_c0c) I) (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F
          (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
            (syn_cop (syn_c0c) I))))
      p0005 p0013
  have p0015 := @g_fnfrec ph F G I hyp_frec0_1 hyp_frec0_2 hyp_frec0_3 hyp_frec0_4
  have p0017 := @g_fnopfvb (syn_cnnc) (syn_c0c) I F
  have p0018 :=
    @g_sylancl ph (syn_wfn F (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))
      (syn_wb (.classEq (syn_cfv F (syn_c0c)) I) (.classMem (syn_cop (syn_c0c) I) F))
      p0015 p0000 p0017
  have p0019 :=
    @g_mpbird ph (.classEq (syn_cfv F (syn_c0c)) I) (.classMem (syn_cop (syn_c0c) I) F)
      p0014 p0018
  exact p0019

@[expose]
noncomputable def g_frecsuc (ph : Wff) (F : Class) (G : Class) (I : Class) (X : Class)
    (hyp_frecsuc_1 : Nominal.NPrf (.classEq F (syn_cfrec G I)))
    (hyp_frecsuc_2 : Nominal.NPrf (.imp ph (.classMem G (syn_cfuns))))
    (hyp_frecsuc_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G))))
    (hyp_frecsuc_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G))))
    (hyp_frecsuc_5 : Nominal.NPrf (.imp ph (.classMem X (syn_cnnc)))) :
    Nominal.NPrf
      (.imp ph (.classEq (syn_cfv F (syn_cplc X (syn_c1c))) (syn_cfv G (syn_cfv F X)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : y ∉ ((syn_cplc (.cv w) (syn_c1c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : w ≠ y := by
    clear dv_cache_0001
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0003 : w ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_X, not_false_eq_true])
  have dv_cache_0004 : y ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_cplc X (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_w_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cplc X (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_y_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    w ∉ ((Wff.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_w_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    y ∉ ((Wff.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_y_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cop X (syn_cfv F X))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_X, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((syn_wa (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
            (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_X, fresh_y_ne_w,
          fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
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
  have dv_cache_0014 :
    y ∉ ((syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_X, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    y ∉ ((syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_w, fresh_y_not_G,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_y_not_I, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_fnfrec ph F G I hyp_frecsuc_1 hyp_frecsuc_2 hyp_frecsuc_3 hyp_frecsuc_4
  have p0001 := @g_fnfun (syn_cnnc) F
  have p0002 := @g_syl ph (syn_wfn F (syn_cnnc)) (syn_wfun F) p0000 p0001
  have p0003 :=
    @g_dmfrec ph F G I (syn_cfuns) hyp_frecsuc_1 hyp_frecsuc_2 hyp_frecsuc_3 hyp_frecsuc_4
  have p0004 := @g_eleqtrrd ph X (syn_cnnc) (syn_cdm F) hyp_frecsuc_5 p0003
  have p0005 := @g_funfvop X F
  have p0006 :=
    @g_syl2anc ph (syn_wfun F) (.classMem X (syn_cdm F))
      (.classMem (syn_cop X (syn_cfv F X)) F) p0002 p0004 p0005
  have p0007 := @g_eqid (syn_cplc X (syn_c1c))
  have p0008 := @g_peano2 X
  have p0009 :=
    @g_syl ph (.classMem X (syn_cnnc)) (.classMem (syn_cplc X (syn_c1c)) (syn_cnnc))
      hyp_frecsuc_5 p0008
  have p0010 := @g_addceq1 (.cv w) X (syn_c1c)
  have p0011 :=
    @g_eqeq2d (.classEq (.cv w) X) (syn_cplc (.cv w) (syn_c1c)) (syn_cplc X (syn_c1c))
      (.cv y) p0010
  have p0012 := @g_eqeq1 (.cv y) (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))
  have p0013 := @g_mptv w y (syn_cplc (.cv w) (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @g_brabg (.classEq (.cv y) (syn_cplc (.cv w) (syn_c1c)))
      (.classEq (.cv y) (syn_cplc X (syn_c1c)))
      (.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))) w y X
      (syn_cplc X (syn_c1c)) (syn_cnnc) (syn_cnnc)
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0002 p0011 p0012
      p0013
  have p0015 :=
    @g_syl2anc ph (.classMem X (syn_cnnc)) (.classMem (syn_cplc X (syn_c1c)) (syn_cnnc))
      (syn_wb (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_cplc X (syn_c1c))) (.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))))
      hyp_frecsuc_5 p0009 p0014
  have p0016 :=
    @g_mpbiri ph
      (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c)))
      (.classEq (syn_cplc X (syn_c1c)) (syn_cplc X (syn_c1c))) p0007 p0015
  have p0017 := @g_elfunsi G
  have p0018 := @g_syl ph (.classMem G (syn_cfuns)) (syn_wfun G) hyp_frecsuc_2 p0017
  have p0019 := @g_snssd ph I (syn_cdm G) hyp_frecsuc_3
  have p0020 := @g_unssd ph (syn_crn G) (syn_csn I) (syn_cdm G) hyp_frecsuc_4 p0019
  have p0021 := @g_frecxpg F G I (syn_cfuns) hyp_frecsuc_1
  have p0022 :=
    @g_syl ph (.classMem G (syn_cfuns))
      (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) hyp_frecsuc_2
      p0021
  have p0023 := @g_rnss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
  have p0024 :=
    @g_syl ph (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))
      (syn_wss (syn_crn F) (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))))
      p0022 p0023
  have p0025 := @g_rnxpss (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))
  have p0026 :=
    @g_syl6ss ph (syn_crn F)
      (syn_crn (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))
      (syn_cun (syn_crn G) (syn_csn I)) p0024 p0025
  have p0027 := @g_fvelrn X F
  have p0028 :=
    @g_syl2anc ph (syn_wfun F) (.classMem X (syn_cdm F))
      (.classMem (syn_cfv F X) (syn_crn F)) p0002 p0004 p0027
  have p0029 :=
    @g_sseldd ph (syn_crn F) (syn_cun (syn_crn G) (syn_csn I)) (syn_cfv F X) p0026 p0028
  have p0030 :=
    @g_sseldd ph (syn_cun (syn_crn G) (syn_csn I)) (syn_cdm G) (syn_cfv F X) p0020 p0029
  have p0031 := @g_funfvop (syn_cfv F X) G
  have p0032 :=
    @g_syl2anc ph (syn_wfun G) (.classMem (syn_cfv F X) (syn_cdm G))
      (.classMem (syn_cop (syn_cfv F X) (syn_cfv G (syn_cfv F X))) G) p0018 p0030 p0031
  have p0033 := (Nominal.biimpRefl (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))))
  have p0034 :=
    @g_sylibr ph (.classMem (syn_cop (syn_cfv F X) (syn_cfv G (syn_cfv F X))) G)
      (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))) p0032 p0033
  have p0035 :=
    @g_breq1 (.cv y) (syn_cop X (syn_cfv F X))
      (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
  have p0036 :=
    @g_qrpprod X (syn_cfv F X) (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))
      (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G
  have p0037 :=
    @g_syl6bb (.classEq (.cv y) (syn_cop X (syn_cfv F X)))
      (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))
      (syn_wbr (syn_cop X (syn_cfv F X))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))
      (syn_wa (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))))
      p0035 p0036
  have p0038 :=
    @g_rspcev
      (syn_wbr (.cv y) (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
        (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))
      (syn_wa (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c)))
          (syn_cplc X (syn_c1c))) (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X))))
      y (syn_cop X (syn_cfv F X)) F dv_cache_0009 dv_cache_0010 dv_cache_0011 p0037
  have p0039 :=
    @g_syl12anc ph (.classMem (syn_cop X (syn_cfv F X)) F)
      (syn_wbr X (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cplc X (syn_c1c)))
      (syn_wbr (syn_cfv F X) G (syn_cfv G (syn_cfv F X)))
      (syn_wrex y F (syn_wbr (.cv y)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))))
      p0006 p0016 p0034 p0038
  have p0040 :=
    @g_olcd ph
      (syn_wrex y F (syn_wbr (.cv y)
          (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
          (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))))
      (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))
        (syn_csn (syn_cop (syn_c0c) I)))
      p0039
  have p0041 := @g_snex (syn_cop (syn_c0c) I)
  have p0042 := @g_csucex w
  have p0043 :=
    @g_pprodexg (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G (syn_cvv)
      (syn_cfuns)
  have p0044 :=
    @g_sylancr ph
      (.classMem (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) (syn_cvv))
      (.classMem G (syn_cfuns))
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      p0042 hyp_frecsuc_2 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec w G I
      dv_cache_0012 dv_cache_0013
  have p0046 :=
    @g_eqtri F (syn_cfrec G I)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G))
      hyp_frecsuc_1 p0045
  have p0047 :=
    @g_clos1basesucg y (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F
      (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv) (syn_cvv) dv_cache_0014 dv_cache_0010
      dv_cache_0015 dv_cache_0016 p0046
  have p0048 :=
    @g_sylancr ph (.classMem (syn_csn (syn_cop (syn_c0c) I)) (syn_cvv))
      (.classMem (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G) (syn_cvv))
      (syn_wb (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F) (syn_wo
          (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))
            (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y)
              (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
              (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))))))
      p0041 p0044 p0047
  have p0049 :=
    @g_mpbird ph (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F)
      (syn_wo (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)))
          (syn_csn (syn_cop (syn_c0c) I))) (syn_wrex y F (syn_wbr (.cv y)
            (syn_cpprod (syn_cmpt w (syn_cvv) (syn_cplc (.cv w) (syn_c1c))) G)
            (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))))))
      p0040 p0048
  have p0050 := @g_fnopfvb (syn_cnnc) (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X)) F
  have p0051 :=
    @g_syl2anc ph (syn_wfn F (syn_cnnc)) (.classMem (syn_cplc X (syn_c1c)) (syn_cnnc))
      (syn_wb (.classEq (syn_cfv F (syn_cplc X (syn_c1c))) (syn_cfv G (syn_cfv F X)))
        (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F))
      p0000 p0009 p0050
  have p0052 :=
    @g_mpbird ph (.classEq (syn_cfv F (syn_cplc X (syn_c1c))) (syn_cfv G (syn_cfv F X)))
      (.classMem (syn_cop (syn_cplc X (syn_c1c)) (syn_cfv G (syn_cfv F X))) F) p0049 p0051
  exact p0052

@[expose]
noncomputable def g_wppcg (A : Class) (B : Class) (f : Var) (g : Var) (h : Var)
    (V : Class) (W : Class) (_dv_A_V : Disjoint A.fv V.fv) (_dv_A_W : Disjoint A.fv W.fv)
    (dv_A_f : f ∉ A.fv) (dv_A_g : g ∉ A.fv) (dv_A_h : h ∉ A.fv)
    (_dv_B_V : Disjoint B.fv V.fv) (_dv_B_W : Disjoint B.fv W.fv) (dv_B_f : f ∉ B.fv)
    (dv_B_g : g ∉ B.fv) (dv_B_h : h ∉ B.fv) (_dv_V_W : Disjoint V.fv W.fv)
    (dv_f_g : f ≠ g) (dv_f_h : f ≠ h) (dv_g_h : g ≠ h) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.imp (syn_wwpp) (.imp
            (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A)))
            (syn_wex h (syn_wf1 (.cv h) A B))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ B.fv ∪ ({ f } : Finset Var) ∪ ({ g } : Finset Var) ∪ ({ h } : Finset Var) ∪
        V.fv ∪
      W.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_y_ne_h : y ≠ h := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_x : g ≠ x := Ne.symm fresh_x_ne_g
  have fresh_x_ne_h : x ≠ h := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_h_ne_x : h ≠ x := Ne.symm fresh_x_ne_h
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : f ≠ g := by exact (show f ≠ g from (by exact dv_f_g))
  have dv_cache_0002 : f ≠ h := by
    clear dv_cache_0001
    exact (show f ≠ h from (by exact dv_f_h))
  have dv_cache_0003 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0004 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0005 : g ≠ h :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show g ≠ h from (by exact dv_g_h))
  have dv_cache_0006 : g ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0007 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0008 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0009 : h ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ y from (by exact fresh_h_ne_y))
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : f ∉ ((syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, dv_A_f, fresh_f_ne_y, dv_B_f, or_false,
          not_false_eq_true])
  have dv_cache_0012 : g ∉ ((syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_x, dv_A_g, fresh_g_ne_y, dv_B_g, or_false,
          not_false_eq_true])
  have dv_cache_0013 : h ∉ ((syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, dv_A_h, fresh_h_ne_y, dv_B_h, or_false,
          not_false_eq_true])
  have dv_cache_0014 : x ∉ (A).fv :=
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
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv :=
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0016 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0017 : y ∉ (B).fv :=
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
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((Wff.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A)))
          (syn_wex h (syn_wf1 (.cv h) A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_A,
          fresh_x_ne_f, fresh_x_ne_g, fresh_x_ne_h, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0019 :
    y ∉
      ((Wff.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A)))
          (syn_wex h (syn_wf1 (.cv h) A B)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A,
          fresh_y_ne_f, fresh_y_ne_g, fresh_y_ne_h, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wpp x y f g h
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @g_biimpi (syn_wwpp)
      (.all x (.all y (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
              (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
            (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))))))
      p0000
  have p0002 := @g_foeq3 (.cv x) A (.cv y) (.cv f)
  have p0003 := @g_foeq2 (.cv y) B A (.cv f)
  have p0004 :=
    @g_sylan9bb (.classEq (.cv x) A) (syn_wfo (.cv f) (.cv y) (.cv x))
      (syn_wfo (.cv f) (.cv y) A) (.classEq (.cv y) B) (syn_wfo (.cv f) B A) p0002 p0003
  have p0005 :=
    @g_exbidv (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wfo (.cv f) (.cv y) (.cv x)) (syn_wfo (.cv f) B A) f dv_cache_0011 p0004
  have p0006 := @g_f1eq3 (.cv x) A (.cv y) (.cv g)
  have p0007 := @g_f1eq2 (.cv y) B A (.cv g)
  have p0008 :=
    @g_sylan9bb (.classEq (.cv x) A) (syn_wf1 (.cv g) (.cv y) (.cv x))
      (syn_wf1 (.cv g) (.cv y) A) (.classEq (.cv y) B) (syn_wf1 (.cv g) B A) p0006 p0007
  have p0009 :=
    @g_exbidv (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wf1 (.cv g) (.cv y) (.cv x)) (syn_wf1 (.cv g) B A) g dv_cache_0012 p0008
  have p0010 :=
    @g_anbi12d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x))) (syn_wex f (syn_wfo (.cv f) B A))
      (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))) (syn_wex g (syn_wf1 (.cv g) B A))
      p0005 p0009
  have p0011 := @g_f1eq2 (.cv x) A (.cv y) (.cv h)
  have p0012 := @g_f1eq3 (.cv y) B A (.cv h)
  have p0013 :=
    @g_sylan9bb (.classEq (.cv x) A) (syn_wf1 (.cv h) (.cv x) (.cv y))
      (syn_wf1 (.cv h) A (.cv y)) (.classEq (.cv y) B) (syn_wf1 (.cv h) A B) p0011 p0012
  have p0014 :=
    @g_exbidv (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wf1 (.cv h) (.cv x) (.cv y)) (syn_wf1 (.cv h) A B) h dv_cache_0013 p0013
  have p0015 :=
    @g_imbi12d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
        (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
      (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A)))
      (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))) (syn_wex h (syn_wf1 (.cv h) A B))
      p0010 p0014
  have p0016 :=
    @g_spc2gv
      (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
          (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
        (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))))
      (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A)))
        (syn_wex h (syn_wf1 (.cv h) A B)))
      x y A B V W dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0010 p0015
  have p0017 :=
    @g_syl5 (syn_wwpp)
      (.all x (.all y (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) (.cv y) (.cv x)))
              (syn_wex g (syn_wf1 (.cv g) (.cv y) (.cv x))))
            (syn_wex h (syn_wf1 (.cv h) (.cv x) (.cv y))))))
      (syn_wa (.classMem A V) (.classMem B W))
      (.imp (syn_wa (syn_wex f (syn_wfo (.cv f) B A)) (syn_wex g (syn_wf1 (.cv g) B A)))
        (syn_wex h (syn_wf1 (.cv h) A B)))
      p0001 p0016
  exact p0017

@[expose]
noncomputable def g_nnnzdf (y : Var) :
    Nominal.NPrf
      (.classEq (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
        (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0001 := @g_peano1
  have p0002 := @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c))
      (syn_cnnc) p0003
  have p0005 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_nnnzex (y : Var) :
    Nominal.NPrf
      (.classMem (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_cvv)) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0001 := @g_peano1
  have p0002 := @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c))
      (syn_cnnc) p0003
  have p0005 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0000 p0004
  have p0006 := @g_nncex
  have p0007 := @g_snex (syn_c0c)
  have p0008 := @g_difex (syn_cnnc) (syn_csn (syn_c0c)) p0006 p0007
  have p0009 :=
    @g_eqeltri (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_cvv) p0005 p0008
  exact p0009

@[expose]
noncomputable def g_fopprod (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfo F A C) (syn_wfo G B D))
        (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))) :=
  by
  have p0000 := @g_simpl (syn_wfo F A C) (syn_wfo G B D)
  have p0001 := @g_fofn A C F
  have p0002 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C) (syn_wfn F A) p0000
      p0001
  have p0003 := @g_simpr (syn_wfo F A C) (syn_wfo G B D)
  have p0004 := @g_fofn B D G
  have p0005 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D) (syn_wfn G B) p0003
      p0004
  have p0006 :=
    @g_jca (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfn F A) (syn_wfn G B) p0002
      p0005
  have p0007 := @g_fnpprod A B F G
  have p0008 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wa (syn_wfn F A) (syn_wfn G B))
      (syn_wfn (syn_cpprod F G) (syn_cxp A B)) p0006 p0007
  have p0009 := @g_rnpprod F G
  have p0010 :=
    @g_a1i (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp (syn_crn F) (syn_crn G)))
      (syn_wa (syn_wfo F A C) (syn_wfo G B D)) p0009
  have p0012 := @g_forn A C F
  have p0013 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C)
      (.classEq (syn_crn F) C) p0000 p0012
  have p0015 := @g_forn B D G
  have p0016 :=
    @g_syl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D)
      (.classEq (syn_crn G) D) p0003 p0015
  have p0017 :=
    @g_xpeq12d (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_crn F) C (syn_crn G) D p0013
      p0016
  have p0018 :=
    @g_eqtrd (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_crn (syn_cpprod F G))
      (syn_cxp (syn_crn F) (syn_crn G)) (syn_cxp C D) p0010 p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wfo F A C) (syn_wfo G B D))
      (syn_wfn (syn_cpprod F G) (syn_cxp A B))
      (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp C D)) p0008 p0018
  have p0020 := (Nominal.biimpRefl (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D)))
  have p0021 :=
    @g_a1i
      (syn_wb (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))
        (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B))
          (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp C D))))
      (syn_wa (syn_wfo F A C) (syn_wfo G B D)) p0020
  have p0022 :=
    @g_mpbird (syn_wa (syn_wfo F A C) (syn_wfo G B D))
      (syn_wfo (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))
      (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B))
        (.classEq (syn_crn (syn_cpprod F G)) (syn_cxp C D)))
      p0019 p0021
  exact p0022

@[expose]
noncomputable def g_foun (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
        (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D))) :=
  by
  have p0000 :=
    @g_simpl (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0001 := @g_simpl (syn_wfo F A C) (syn_wfo G B D)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo F A C) p0000 p0001
  have p0003 := @g_fofn A C F
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfo F A C) (syn_wfn F A) p0002 p0003
  have p0006 := @g_simpr (syn_wfo F A C) (syn_wfo G B D)
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (syn_wfo G B D) p0000 p0006
  have p0008 := @g_fofn B D G
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfo G B D) (syn_wfn G B) p0007 p0008
  have p0010 :=
    @g_jca
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfn F A) (syn_wfn G B) p0004 p0009
  have p0011 :=
    @g_simpr (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0))
  have p0012 :=
    @g_jca
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)) p0010 p0011
  have p0013 := @g_fnun A B F G
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfn (syn_cun F G) (syn_cun A B)) p0012 p0013
  have p0015 := @g_rnun F G
  have p0016 :=
    @g_a1i (.classEq (syn_crn (syn_cun F G)) (syn_cun (syn_crn F) (syn_crn G)))
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      p0015
  have p0020 := @g_forn A C F
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfo F A C) (.classEq (syn_crn F) C) p0002 p0020
  have p0025 := @g_forn B D G
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfo G B D) (.classEq (syn_crn G) D) p0007 p0025
  have p0027 :=
    @g_uneq12d
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_crn F) C (syn_crn G) D p0021 p0026
  have p0028 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_crn (syn_cun F G)) (syn_cun (syn_crn F) (syn_crn G)) (syn_cun C D) p0016 p0027
  have p0029 :=
    @g_jca
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfn (syn_cun F G) (syn_cun A B))
      (.classEq (syn_crn (syn_cun F G)) (syn_cun C D)) p0014 p0028
  have p0030 := (Nominal.biimpRefl (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D)))
  have p0031 :=
    @g_a1i
      (syn_wb (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D))
        (syn_wa (syn_wfn (syn_cun F G) (syn_cun A B))
          (.classEq (syn_crn (syn_cun F G)) (syn_cun C D))))
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      p0030
  have p0032 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wfo F A C) (syn_wfo G B D)) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wfo (syn_cun F G) (syn_cun A B) (syn_cun C D))
      (syn_wa (syn_wfn (syn_cun F G) (syn_cun A B))
        (.classEq (syn_crn (syn_cun F G)) (syn_cun C D)))
      p0029 p0031
  exact p0032

@[expose]
noncomputable def g_xnnex (x : Var) :
    Nominal.NPrf (.classMem (syn_cxp (.cv x) (syn_cnnc)) (syn_cvv)) :=
  by
  have p0000 := @g_vex x
  have p0001 := @g_nncex
  have p0002 := @g_xpex (.cv x) (syn_cnnc) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_padsetex (x : Var) (y : Var) (v : Var) (_dv_v_x : v ≠ x)
    (_dv_v_y : v ≠ y) (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cvv)) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_vex v
  have p0001 := @g_snex (syn_c0c)
  have p0002 := @g_xpex (.cv v) (syn_csn (syn_c0c)) p0000 p0001
  have p0003 := @g_vex x
  have p0004 := @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0005 := @g_peano1
  have p0006 := @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c))
      (syn_cnnc) p0007
  have p0009 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0004 p0008
  have p0010 := @g_nncex
  have p0012 := @g_difex (syn_cnnc) (syn_csn (syn_c0c)) p0010 p0001
  have p0013 :=
    @g_eqeltri (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_cvv) p0009 p0012
  have p0014 :=
    @g_xpex (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0003
      p0013
  have p0015 :=
    @g_unex (syn_cxp (.cv v) (syn_csn (syn_c0c)))
      (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0002
      p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_xnndisj (y : Var) (X : Class) (_dv_X_y : y ∉ X.fv) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cxp X (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_c0)) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_disjdif (syn_csn (syn_c0c)) (syn_cnnc)
  have p0001 :=
    @g_xpdisj2 (syn_csn (syn_c0c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) X X
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0004 := @g_peano1
  have p0005 := @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c))
      (syn_cnnc) p0006
  have p0008 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0003 p0007
  have p0009 :=
    @g_eqcomi (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0008
  have p0010 :=
    @g_xpeq2i (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) X p0009
  have p0011 :=
    @g_ineq2i (syn_cxp X (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))))
      (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cxp X (syn_csn (syn_c0c))) p0010
  have p0012 :=
    @g_eqtr3i
      (syn_cin (syn_cxp X (syn_csn (syn_c0c)))
        (syn_cxp X (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))))
      (syn_c0)
      (syn_cin (syn_cxp X (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      p0002 p0011
  have p0013 :=
    @g_eqcomi (syn_c0)
      (syn_cin (syn_cxp X (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      p0012
  exact p0013

@[expose]
noncomputable def g_xnnun (y : Var) (X : Class) (_dv_X_y : y ∉ X.fv) :
    Nominal.NPrf
      (.classEq (syn_cun (syn_cxp X (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cxp X (syn_cnnc))) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_undif2 (syn_csn (syn_c0c)) (syn_cnnc)
  have p0001 := @g_peano1
  have p0002 := @g_snssi (syn_c0c) (syn_cnnc)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_ssequn1 (syn_csn (syn_c0c)) (syn_cnnc)
  have p0005 :=
    @g_mpbi (syn_wss (syn_csn (syn_c0c)) (syn_cnnc))
      (.classEq (syn_cun (syn_csn (syn_c0c)) (syn_cnnc)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_eqtri (syn_cun (syn_csn (syn_c0c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))))
      (syn_cun (syn_csn (syn_c0c)) (syn_cnnc)) (syn_cnnc) p0000 p0005
  have p0007 := @g_notrab (.classEq (.cv y) (syn_c0c)) y (syn_cnnc) dv_cache_0001
  have p0009 := @g_rabsn y (syn_cnnc) (syn_c0c) dv_cache_0001 dv_cache_0002
  have p0010 := Nominal.mp p0001 p0009
  have p0011 :=
    @g_difeq2i (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))) (syn_csn (syn_c0c))
      (syn_cnnc) p0010
  have p0012 :=
    @g_eqtr3i (syn_cdif (syn_cnnc) (syn_crab y (syn_cnnc) (.classEq (.cv y) (syn_c0c))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0007 p0011
  have p0013 :=
    @g_eqcomi (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) p0012
  have p0014 :=
    @g_uneq2i (syn_cdif (syn_cnnc) (syn_csn (syn_c0c)))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) (syn_csn (syn_c0c))
      p0013
  have p0015 :=
    @g_eqtr3i (syn_cun (syn_csn (syn_c0c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))))
      (syn_cnnc)
      (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      p0006 p0014
  have p0016 :=
    @g_eqcomi (syn_cnnc)
      (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      p0015
  have p0017 :=
    @g_xpeq2i
      (syn_cun (syn_csn (syn_c0c)) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cnnc) X p0016
  have p0018 :=
    @g_xpundi X (syn_csn (syn_c0c))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
  have p0019 :=
    @g_eqtr3i
      (syn_cxp X (syn_cun (syn_csn (syn_c0c))
          (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cxp X (syn_cnnc))
      (syn_cun (syn_cxp X (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      p0017 p0018
  have p0020 :=
    @g_eqcomi (syn_cxp X (syn_cnnc))
      (syn_cun (syn_cxp X (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      p0019
  exact p0020

@[expose]
noncomputable def g_sucnnf1o (y : Var) (z : Var) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wf1o (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : z ∉ ((syn_cnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_y_z),
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
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
  have dv_cache_0004 : z ∉ ((syn_cplc (.cv w) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cplc (.cv t) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : w ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0009 : w ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_z, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cplc (.cv z) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, dv_y_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show z ≠ y from (by exact Ne.symm dv_y_z))
  have dv_cache_0015 : z ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_y_z), not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_wne (.cv y) (syn_c0c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_y_z), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_eqid (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0001 := @g_peano2 (.cv z)
  have p0002 := @g_peano3 (.cv z)
  have p0003 :=
    @g_jca (.classMem (.cv z) (syn_cnnc))
      (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc))
      (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c)) p0001 p0002
  have p0004 := @g_nnnzdf y
  have p0005 :=
    @g_eleq2i (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))) (syn_cplc (.cv z) (syn_c1c)) p0004
  have p0006 := @g_eldifsn (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc) (syn_c0c)
  have p0007 :=
    @g_bitri
      (.classMem (syn_cplc (.cv z) (syn_c1c))
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0c))))
      (syn_wa (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc))
        (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c)))
      p0005 p0006
  have p0008 :=
    @g_sylibr (.classMem (.cv z) (syn_cnnc))
      (syn_wa (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc))
        (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c)))
      (.classMem (syn_cplc (.cv z) (syn_c1c))
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      p0003 p0007
  have p0009 :=
    @g_fmpti z (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cplc (.cv z) (syn_c1c)) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
      dv_cache_0001 dv_cache_0002 p0000 p0008
  have p0010 := @g_addceq1 (.cv z) (.cv w) (syn_c1c)
  have p0012 := @g_vex w
  have p0013 := @g_n_1cex
  have p0014 := @g_addcex (.cv w) (syn_c1c) p0012 p0013
  have p0015 :=
    @g_fvmpt z (.cv w) (syn_cplc (.cv z) (syn_c1c)) (syn_cplc (.cv w) (syn_c1c))
      (syn_cnnc) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0003
      dv_cache_0004 dv_cache_0001 p0010 p0000 p0014
  have p0016 :=
    @g_adantr (.classMem (.cv w) (syn_cnnc))
      (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
        (syn_cplc (.cv w) (syn_c1c)))
      (.classMem (.cv t) (syn_cnnc)) p0015
  have p0017 := @g_addceq1 (.cv z) (.cv t) (syn_c1c)
  have p0019 := @g_vex t
  have p0021 := @g_addcex (.cv t) (syn_c1c) p0019 p0013
  have p0022 :=
    @g_fvmpt z (.cv t) (syn_cplc (.cv z) (syn_c1c)) (syn_cplc (.cv t) (syn_c1c))
      (syn_cnnc) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0005
      dv_cache_0006 dv_cache_0001 p0017 p0000 p0021
  have p0023 :=
    @g_adantl (.classMem (.cv t) (syn_cnnc))
      (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))
        (syn_cplc (.cv t) (syn_c1c)))
      (.classMem (.cv w) (syn_cnnc)) p0022
  have p0024 :=
    @g_eqeq12d (syn_wa (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv t) (syn_cnnc)))
      (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
      (syn_cplc (.cv w) (syn_c1c))
      (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t))
      (syn_cplc (.cv t) (syn_c1c)) p0016 p0023
  have p0025 := @g_suc11nnc (.cv w) (.cv t)
  have p0026 :=
    @g_bitrd (syn_wa (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv t) (syn_cnnc)))
      (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
        (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)))
      (.classEq (syn_cplc (.cv w) (syn_c1c)) (syn_cplc (.cv t) (syn_c1c)))
      (.classEq (.cv w) (.cv t)) p0024 p0025
  have p0027 :=
    @g_biimpd (syn_wa (.classMem (.cv w) (syn_cnnc)) (.classMem (.cv t) (syn_cnnc)))
      (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
        (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)))
      (.classEq (.cv w) (.cv t)) p0026
  have p0028 :=
    @g_rgen2
      (.imp (.classEq (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
          (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)))
        (.classEq (.cv w) (.cv t)))
      w t (syn_cnnc) (syn_cnnc) dv_cache_0007 dv_cache_0008 p0027
  have p0029 :=
    @g_pm3_2i
      (syn_wf (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_wral w (syn_cnnc) (syn_wral t (syn_cnnc) (.imp (.classEq
              (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
              (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)))
            (.classEq (.cv w) (.cv t)))))
      p0009 p0028
  have p0030 :=
    @g_dff13 w t (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0009 dv_cache_0007
      dv_cache_0010 dv_cache_0011 dv_cache_0008
  have p0031_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
          (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wa
          (syn_wf (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
            (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wral w (syn_cnnc)
            (syn_wral t (syn_cnnc) (.imp (.classEq
                  (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
                  (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)))
                (.classEq (.cv w) (.cv t))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cmpt syn_cnnc syn_cint
          syn_cplc syn_wrex syn_c1c syn_crab syn_c0c syn_csn syn_c0 syn_cdif syn_cvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @g_mpbir
      (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_wa (syn_wf (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
          (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) (syn_wral w (syn_cnnc)
          (syn_wral t (syn_cnnc) (.imp (.classEq
                (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv w))
                (syn_cfv (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (.cv t)))
              (.classEq (.cv w) (.cv t))))))
      p0029 p0031_e01_recanon
  have p0033 :=
    @g_rnmpt z y (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))
      (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) dv_cache_0012 dv_cache_0013
      dv_cache_0014 p0000
  have p0034 :=
    @g_olc (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (.classEq (.cv y) (syn_c0c))
  have p0035 := @g_nnc0suc z (.cv y) dv_cache_0015
  have p0036 :=
    @g_sylibr (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (syn_wo (.classEq (.cv y) (syn_c0c))
        (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))))
      (.classMem (.cv y) (syn_cnnc)) p0034 p0035
  have p0037 :=
    @g_simpr (.classMem (.cv z) (syn_cnnc))
      (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))
  have p0039 :=
    @g_adantr (.classMem (.cv z) (syn_cnnc))
      (syn_wne (syn_cplc (.cv z) (syn_c1c)) (syn_c0c))
      (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))) p0002
  have p0040 :=
    @g_eqnetrd
      (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (.cv y) (syn_cplc (.cv z) (syn_c1c)) (syn_c0c) p0037 p0039
  have p0041 :=
    @g_ex (.classMem (.cv z) (syn_cnnc)) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))
      (syn_wne (.cv y) (syn_c0c)) p0040
  have p0042 :=
    @g_rexlimiv (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))
      (syn_wne (.cv y) (syn_c0c)) z (syn_cnnc) dv_cache_0016 p0041
  have p0043 := (Nominal.biimpRefl (syn_wne (.cv y) (syn_c0c)))
  have p0044 :=
    @g_sylib (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (syn_wne (.cv y) (syn_c0c)) (.neg (.classEq (.cv y) (syn_c0c))) p0042 p0043
  have p0045 :=
    @g_jca (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c))) p0036 p0044
  have p0046 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))
  have p0047 :=
    @g_pm2_21d (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c))))
      (.classEq (.cv y) (syn_c0c))
      (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) p0046
  have p0048 :=
    @g_id (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
  have p0049 :=
    @g_a1i
      (.imp (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
        (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))))
      (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) p0048
  have p0050 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))
  have p0052 :=
    @g_biimpi (.classMem (.cv y) (syn_cnnc))
      (syn_wo (.classEq (.cv y) (syn_c0c))
        (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))))
      p0035
  have p0053 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c))))
      (.classMem (.cv y) (syn_cnnc))
      (syn_wo (.classEq (.cv y) (syn_c0c))
        (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))))
      p0050 p0052
  have p0054 :=
    @g_mpjaod (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c))))
      (.classEq (.cv y) (syn_c0c))
      (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))) p0047 p0049
      p0053
  have p0055 :=
    @g_impbii (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) p0045
      p0054
  have p0056 :=
    @g_abbii (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c))))
      (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))) y p0055
  have p0057 :=
    (Nominal.classEqRefl (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
  have p0058 :=
    @g_eqtr4i
      (.cab y (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))))
      (.cab y (syn_wa (.classMem (.cv y) (syn_cnnc)) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0056 p0057
  have p0059 :=
    @g_eqtri (syn_crn (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
      (.cab y (syn_wrex z (syn_cnnc) (.classEq (.cv y) (syn_cplc (.cv z) (syn_c1c)))))
      (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0033 p0058
  have p0060 :=
    @g_pm3_2i
      (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (.classEq (syn_crn (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      p0031 p0059
  have p0061 :=
    @g_dff1o5 (syn_cnnc) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0062 :=
    @g_mpbir
      (syn_wf1o (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_wa (syn_wf1 (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
          (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
        (.classEq (syn_crn (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
          (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      p0060 p0061
  exact p0062

@[expose]
noncomputable def g_padontoex (x : Var) (y : Var) (v : Var) (f : Var) (F : Class)
    (dv_F_f : f ∉ F.fv) (_dv_F_v : v ∉ F.fv) (_dv_F_x : x ∉ F.fv) (_dv_F_y : y ∉ F.fv)
    (dv_f_v : f ≠ v) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (_dv_v_x : v ≠ x) (_dv_v_y : v ≠ y)
    (_dv_x_y : x ≠ y) (hyp_padontoex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
            (syn_cres (syn_cid) (syn_cxp (.cv x)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
          (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv x) (syn_cnnc))
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) :=
  by
  have dv_cache_0001 :
    f ∉
      ((syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid)
            (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_F_f, dv_f_x, dv_f_y, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0002 :
    f ∉
      ((syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
            (syn_cres (syn_cid) (syn_cxp (.cv x)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
          (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_f_x, dv_f_v, dv_f_y, dv_F_f, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_idex
  have p0001 := @g_snex (syn_c0c)
  have p0002 := @g_resex (syn_cid) (syn_csn (syn_c0c)) p0000 p0001
  have p0003 := @g_pprodexg F (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_cvv) (syn_cvv)
  have p0004 :=
    @g_mpan2 (.classMem F (syn_cvv))
      (.classMem (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_cvv))
      (.classMem (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cvv)) p0002
      p0003
  have p0006 := @g_vex x
  have p0007 := @g_nnnzex y
  have p0008 :=
    @g_xpex (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))) p0006
      p0007
  have p0009 :=
    @g_resex (syn_cid)
      (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))) p0000
      p0008
  have p0010 :=
    @g_a1i
      (.classMem (syn_cres (syn_cid)
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cvv))
      (.classMem F (syn_cvv)) p0009
  have p0011 :=
    @g_jca (.classMem F (syn_cvv))
      (.classMem (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cvv))
      (.classMem (syn_cres (syn_cid)
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cvv))
      p0004 p0010
  have p0012 :=
    @g_unexg (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
      (syn_cres (syn_cid)
        (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem F (syn_cvv))
      (syn_wa (.classMem (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cvv))
        (.classMem (syn_cres (syn_cid)
            (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
          (syn_cvv)))
      (.classMem (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid) (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cvv))
      p0011 p0012
  have p0014 :=
    @g_foeq1 (syn_cxp (.cv x) (syn_cnnc))
      (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (.cv f)
      (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid)
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
  have p0015 :=
    @g_spcegv
      (syn_wfo (.cv f) (syn_cxp (.cv x) (syn_cnnc))
        (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid) (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      f
      (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid)
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (syn_cvv) dv_cache_0001 dv_cache_0002 p0014
  have p0016 :=
    @g_syl (.classMem F (syn_cvv))
      (.classMem (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid) (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cvv))
      (.imp (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
            (syn_cres (syn_cid) (syn_cxp (.cv x)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
          (syn_cxp (.cv x) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv x) (syn_cnnc))
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))))
      p0013 p0015
  have p0017 := Nominal.mp hyp_padontoex_1 p0016
  exact p0017

@[expose]
noncomputable def g_sucxpinjex (x : Var) (y : Var) (z : Var) (v : Var) (g : Var)
    (dv_g_v : g ≠ v) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_g_z : g ≠ z) (_dv_v_x : v ≠ x)
    (_dv_v_y : v ≠ y) (_dv_v_z : v ≠ z) (_dv_x_y : x ≠ y) (_dv_x_z : x ≠ z)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wf1 (syn_cpprod (syn_cres (syn_cid) (.cv x))
            (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp (.cv x) (syn_cnnc))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wex g
          (syn_wf1 (.cv g) (syn_cxp (.cv x) (syn_cnnc))
            (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x)
                (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) :=
  by
  have dv_cache_0001 : z ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 :
    g ∉
      ((syn_cpprod (syn_cres (syn_cid) (.cv x))
          (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_g_x, dv_g_z,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0004 :
    g ∉
      ((syn_wf1 (syn_cpprod (syn_cres (syn_cid) (.cv x))
            (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp (.cv x) (syn_cnnc))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_g_x, dv_g_v, dv_g_y, dv_g_z, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_idex
  have p0001 := @g_vex x
  have p0002 := @g_resex (syn_cid) (.cv x) p0000 p0001
  have p0003 := @g_ssv (syn_cnnc)
  have p0004 :=
    @g_resmpt z (syn_cvv) (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)) dv_cache_0001
      dv_cache_0002
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_csucex z
  have p0007 := @g_nncex
  have p0008 :=
    @g_resex (syn_cmpt z (syn_cvv) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc) p0006 p0007
  have p0009 :=
    @g_eqeltrri (syn_cres (syn_cmpt z (syn_cvv) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc))
      (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cvv) p0005 p0008
  have p0010 :=
    @g_pprodex (syn_cres (syn_cid) (.cv x))
      (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) p0002 p0009
  have p0011 :=
    @g_f1eq1 (syn_cxp (.cv x) (syn_cnnc))
      (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (.cv g)
      (syn_cpprod (syn_cres (syn_cid) (.cv x))
        (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
  have p0012 :=
    @g_spcev
      (syn_wf1 (.cv g) (syn_cxp (.cv x) (syn_cnnc))
        (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (syn_wf1 (syn_cpprod (syn_cres (syn_cid) (.cv x))
          (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp (.cv x) (syn_cnnc))
        (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      g
      (syn_cpprod (syn_cres (syn_cid) (.cv x))
        (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
      dv_cache_0003 dv_cache_0004 p0010 p0011
  exact p0012

@[expose]
noncomputable def g_sucxpinj (y : Var) (z : Var) (V : Class) (X : Class)
    (_dv_V_X : Disjoint V.fv X.fv) (_dv_V_y : y ∉ V.fv) (_dv_V_z : z ∉ V.fv)
    (_dv_X_y : y ∉ X.fv) (_dv_X_z : z ∉ X.fv) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wf1 (syn_cpprod (syn_cres (syn_cid) X)
          (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp X (syn_cnnc))
        (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) :=
  by
  have dv_cache_0001 : y ≠ z := by exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @g_f1oi X
  have p0001 := @g_sucnnf1o y z dv_cache_0001
  have p0002 :=
    @g_pm3_2i (syn_wf1o (syn_cres (syn_cid) X) X X)
      (syn_wf1o (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))) (syn_cnnc)
        (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      p0000 p0001
  have p0003 :=
    @g_f1opprod X (syn_cnnc) X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))
      (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_f1of1 (syn_cxp X (syn_cnnc))
      (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cpprod (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_ssun2 (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cxp V (syn_csn (syn_c0c)))
  have p0008 :=
    @g_pm3_2i
      (syn_wf1 (syn_cpprod (syn_cres (syn_cid) X)
          (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c)))) (syn_cxp X (syn_cnnc))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_wss (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
        (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      p0006 p0007
  have p0009 :=
    @g_f1ss (syn_cxp X (syn_cnnc))
      (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cpprod (syn_cres (syn_cid) X) (syn_cmpt z (syn_cnnc) (syn_cplc (.cv z) (syn_c1c))))
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

@[expose]
noncomputable def g_wpppadonto (y : Var) (F : Class) (V : Class) (X : Class)
    (_dv_F_V : Disjoint F.fv V.fv) (_dv_F_X : Disjoint F.fv X.fv) (_dv_F_y : y ∉ F.fv)
    (_dv_V_X : Disjoint V.fv X.fv) (_dv_V_y : y ∉ V.fv) (dv_X_y : y ∉ X.fv) :
    Nominal.NPrf
      (.imp (syn_wfo F X V) (syn_wfo
          (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid)
              (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
          (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) :=
  by
  have dv_cache_0001 : y ∉ (X).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_y, not_false_eq_true])
  have p0000 := @g_id (syn_wfo F X V)
  have p0001 := @g_f1oi (syn_csn (syn_c0c))
  have p0002 :=
    @g_f1ofo (syn_csn (syn_c0c)) (syn_csn (syn_c0c))
      (syn_cres (syn_cid) (syn_csn (syn_c0c)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_jctir (syn_wfo F X V) (syn_wfo F X V)
      (syn_wfo (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_csn (syn_c0c)) (syn_csn (syn_c0c)))
      p0000 p0003
  have p0005 :=
    @g_fopprod X (syn_csn (syn_c0c)) V (syn_csn (syn_c0c)) F
      (syn_cres (syn_cid) (syn_csn (syn_c0c)))
  have p0006 :=
    @g_syl (syn_wfo F X V)
      (syn_wa (syn_wfo F X V)
        (syn_wfo (syn_cres (syn_cid) (syn_csn (syn_c0c))) (syn_csn (syn_c0c))
          (syn_csn (syn_c0c))))
      (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
        (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c))))
      p0004 p0005
  have p0007 :=
    @g_f1oi (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
  have p0008 :=
    @g_f1ofo (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cres (syn_cid)
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_jctir (syn_wfo F X V)
      (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
        (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c))))
      (syn_wfo (syn_cres (syn_cid)
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      p0006 p0009
  have p0011 := @g_xnndisj y X dv_cache_0001
  have p0012 :=
    @g_jctir (syn_wfo F X V)
      (syn_wa (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c)))) (syn_wfo
          (syn_cres (syn_cid)
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (.classEq (syn_cin (syn_cxp X (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_c0))
      p0010 p0011
  have p0013 :=
    @g_foun (syn_cxp X (syn_csn (syn_c0c)))
      (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cxp V (syn_csn (syn_c0c)))
      (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
      (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
      (syn_cres (syn_cid)
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
  have p0014 :=
    @g_syl (syn_wfo F X V)
      (syn_wa (syn_wa (syn_wfo (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
            (syn_cxp X (syn_csn (syn_c0c))) (syn_cxp V (syn_csn (syn_c0c)))) (syn_wfo
            (syn_cres (syn_cid)
              (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (.classEq
          (syn_cin (syn_cxp X (syn_csn (syn_c0c)))
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_c0)))
      (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid)
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_cun (syn_cxp X (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      p0012 p0013
  have p0015 := @g_xnnun y X dv_cache_0001
  have p0016 :=
    @g_foeq2
      (syn_cun (syn_cxp X (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cxp X (syn_cnnc))
      (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
        (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid)
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_sylib (syn_wfo F X V)
      (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid)
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_cun (syn_cxp X (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
        (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (syn_wfo (syn_cun (syn_cpprod F (syn_cres (syn_cid) (syn_csn (syn_c0c))))
          (syn_cres (syn_cid)
            (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
        (syn_cxp X (syn_cnnc)) (syn_cun (syn_cxp V (syn_csn (syn_c0c)))
          (syn_cxp X (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      p0014 p0017
  exact p0018

@[expose]
noncomputable def g_f1exco (t : Var) (A : Class) (B : Class) (C : Class) (h : Var)
    (k : Var) (dv_A_h : h ∉ A.fv) (dv_A_k : k ∉ A.fv) (dv_A_t : t ∉ A.fv)
    (dv_B_h : h ∉ B.fv) (_dv_B_k : k ∉ B.fv) (dv_B_t : t ∉ B.fv) (dv_C_h : h ∉ C.fv)
    (dv_C_k : k ∉ C.fv) (dv_C_t : t ∉ C.fv) (dv_h_k : h ≠ k) (dv_h_t : h ≠ t)
    (dv_k_t : k ≠ t) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wex h (syn_wf1 (.cv h) B C)) (syn_wex t (syn_wf1 (.cv t) A B)))
        (syn_wex k (syn_wf1 (.cv k) A C))) :=
  by
  have dv_cache_0001 : t ∉ ((syn_wf1 (.cv h) B C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_B_t, dv_C_t, (Ne.symm dv_h_t), or_false,
          not_false_eq_true])
  have dv_cache_0002 : h ∉ ((syn_wf1 (.cv t) A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_h, dv_B_h, dv_h_t, or_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_ccom (.cv h) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_h_k), dv_k_t, or_false, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_wf1 (syn_ccom (.cv h) (.cv t)) A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_k, dv_C_k, (Ne.symm dv_h_k), dv_k_t, or_false,
          not_false_eq_true])
  have dv_cache_0005 : h ∉ ((syn_wex k (syn_wf1 (.cv k) A C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_h, dv_C_h, dv_h_k, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_wex k (syn_wf1 (.cv k) A C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_t, dv_C_t, (Ne.symm dv_k_t), or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @g_eeanv (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B) h t dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpri
      (syn_wex h (syn_wex t (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B))))
      (syn_wa (syn_wex h (syn_wf1 (.cv h) B C)) (syn_wex t (syn_wf1 (.cv t) A B))) p0000
  have p0002 := @g_f1co A B C (.cv h) (.cv t)
  have p0003 := @g_vex h
  have p0004 := @g_vex t
  have p0005 := @g_coex (.cv h) (.cv t) p0003 p0004
  have p0006 := @g_f1eq1 A C (.cv k) (syn_ccom (.cv h) (.cv t))
  have p0007 :=
    @g_spcev (syn_wf1 (.cv k) A C) (syn_wf1 (syn_ccom (.cv h) (.cv t)) A C) k
      (syn_ccom (.cv h) (.cv t)) dv_cache_0003 dv_cache_0004 p0005 p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B))
      (syn_wf1 (syn_ccom (.cv h) (.cv t)) A C) (syn_wex k (syn_wf1 (.cv k) A C)) p0002
      p0007
  have p0009 :=
    @g_exlimivv (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B))
      (syn_wex k (syn_wf1 (.cv k) A C)) h t dv_cache_0005 dv_cache_0006 p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wex h (syn_wf1 (.cv h) B C)) (syn_wex t (syn_wf1 (.cv t) A B)))
      (syn_wex h (syn_wex t (syn_wa (syn_wf1 (.cv h) B C) (syn_wf1 (.cv t) A B))))
      (syn_wex k (syn_wf1 (.cv k) A C)) p0001 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_taginjex (x : Var) (y : Var) (v : Var) (t : Var) (dv_t_v : t ≠ v)
    (_dv_t_x : t ≠ x) (_dv_t_y : t ≠ y) (_dv_v_x : v ≠ x) (_dv_v_y : v ≠ y)
    (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
            (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) :=
  by
  have dv_cache_0001 : t ∉ ((Class.cv v)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_t_v,
          not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cxp (.cv v) (syn_csn (syn_c0c)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_t_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_vex v
  have p0001 := @g_n_0cex
  have p0002 := @g_xpsnen (.cv v) (syn_c0c) p0000 p0001
  have p0003 := @g_ensym (syn_cxp (.cv v) (syn_csn (syn_c0c))) (.cv v)
  have p0004 :=
    @g_mpbi (syn_wbr (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cen) (.cv v))
      (syn_wbr (.cv v) (syn_cen) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) p0002 p0003
  have p0005 :=
    @g_bren (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))) t dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_mpbi (syn_wbr (.cv v) (syn_cen) (syn_cxp (.cv v) (syn_csn (syn_c0c))))
      (syn_wex t (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))) p0004
      p0005
  have p0007 := @g_f1of1 (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))) (.cv t)
  have p0008 :=
    @g_ssun1 (syn_cxp (.cv v) (syn_csn (syn_c0c)))
      (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))
  have p0009 :=
    @g_a1i
      (syn_wss (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))) p0008
  have p0010 :=
    @g_jca (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))
      (syn_wf1 (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))
      (syn_wss (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      p0007 p0009
  have p0011 :=
    @g_f1ss (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c)))
      (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
        (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))
      (.cv t)
  have p0012 :=
    @g_syl (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))
      (syn_wa (syn_wf1 (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))
        (syn_wss (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv x)
              (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))
      (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      p0010 p0011
  have p0013 :=
    @g_eximi (syn_wf1o (.cv t) (.cv v) (syn_cxp (.cv v) (syn_csn (syn_c0c))))
      (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c)))
          (syn_cxp (.cv x) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))
      t p0012
  have p0014 := Nominal.mp p0006 p0013
  exact p0014

@[expose]
noncomputable def g_qkrelbr (A : Class) (B : Class) (C : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (hyp_qkrelbr_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_qkrelbr_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk B C) (syn_cqkrel A)) (.classMem (syn_cop B C) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
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
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
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
  have dv_cache_0007 : x ∉ ((syn_cqkrel A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel,
          fresh_x_not_A, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cqkrel A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel,
          fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0012 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
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
  have dv_cache_0015 : y ∉ ((Wff.classMem (syn_cop B C) A)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_C, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (syn_cop (.cv x) (.cv y)) A)).fv :=
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
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.classMem (syn_cop B (.cv y)) A)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, fresh_x_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0018 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0019 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := @g_opeq1 (.cv x) B (.cv y)
  have p0002 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_cop (.cv x) (.cv y)) (syn_cop B (.cv y)) A p0001
  have p0003 := @g_opeq2 (.cv y) C B
  have p0004 := @g_eleq1d (.classEq (.cv y) C) (syn_cop B (.cv y)) (syn_cop B C) A p0003
  have p0005 :=
    @g_opkelopkab (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop B (.cv y)) A) (.classMem (syn_cop B C) A) z x y (syn_cqkrel A) B
      C dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0004 p0000 p0002 p0004 hyp_qkrelbr_1
      hyp_qkrelbr_2
  exact p0005

@[expose]
noncomputable def g_fdmemval (C : Class) (e : Var) (_dv_C_e : e ∉ C.fv)
    (hyp_fdmemval_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
        (.classMem C (.cv e))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdmem))
  have p0001 :=
    @g_eleq2i (syn_cfdmem) (syn_ccnvk (syn_csik (syn_cssetk)))
      (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) p0000
  have p0002 := @g_snex (.cv e)
  have p0003 := @g_snex (syn_csn C)
  have p0004 :=
    @g_opkelcnvk (syn_csn (.cv e)) (syn_csn (syn_csn C)) (syn_csik (syn_cssetk)) p0002
      p0003
  have p0005 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C)))
        (syn_ccnvk (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk)))
      p0001 p0004
  have p0006 := @g_snex C
  have p0007 := @g_vex e
  have p0008 := @g_opksnelsik (syn_csn C) (.cv e) (syn_cssetk) p0006 p0007
  have p0009 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) p0005 p0008
  have p0011 := @g_elssetk C (.cv e) hyp_fdmemval_1 p0007
  have p0012 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) (.classMem C (.cv e)) p0009
      p0011
  exact p0012

@[expose]
noncomputable def g_qkrelex (A : Class)
    (hyp_qkrelex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cqkrel A) (syn_cvv)) :=
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
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
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
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_setconslem6 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0002 :=
    @g_eqtr4i (syn_cqkrel A)
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.classMem (syn_cop (.cv x) (.cv y)) A)))))
      (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
                  (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A)))
      p0000 p0001
  have p0003 := @g_vvex
  have p0006 := @g_xpkex (syn_cvv) (syn_cvv) p0003 p0003
  have p0007 := @g_xpkex (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 := @g_setconslem5
  have p0009 :=
    @g_inex (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
            (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0007 p0008
  have p0010 := @g_pw1ex A hyp_qkrelex_1
  have p0011 := @g_pw1ex (syn_cpw1 A) p0010
  have p0012 :=
    @g_imakex
      (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cpw1 (syn_cpw1 A)) p0009 p0011
  have p0013 :=
    @g_eqeltri (syn_cqkrel A)
      (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
                  (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A)))
      (syn_cvv) p0002 p0012
  exact p0013

@[expose]
noncomputable def g_fdmemex : Nominal.NPrf (.classMem (syn_cfdmem) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdmem))
  have p0001 := @g_ssetkex
  have p0002 := @g_sikex (syn_cssetk) p0001
  have p0003 := @g_cnvkex (syn_csik (syn_cssetk)) p0002
  have p0004 :=
    @g_eqeltri (syn_cfdmem) (syn_ccnvk (syn_csik (syn_cssetk))) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_fdprj0ex : Nominal.NPrf (.classMem (syn_cfdprj0) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdprj0))
  have p0001 := @g_idkex
  have p0002 := @g_ins3kex (syn_cidk) p0001
  have p0003 := @g_eqeltri (syn_cfdprj0) (syn_cins3k (syn_cidk)) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_fdprj1ex : Nominal.NPrf (.classMem (syn_cfdprj1) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdprj1))
  have p0001 := @g_idkex
  have p0002 := @g_ins2kex (syn_cidk) p0001
  have p0003 := @g_eqeltri (syn_cfdprj1) (syn_cins2k (syn_cidk)) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_fddomex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfddom A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfddom A B))
  have p0001 := @g_pw1ex A hyp_fddomex_1
  have p0002 := @g_xpkex B B hyp_fddomex_2 hyp_fddomex_2
  have p0003 := @g_xpkex (syn_cpw1 A) (syn_cxpk B B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)) (syn_cvv) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_fde0ex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfde0 A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfde0 A B))
  have p0001 := @g_fdprj0ex
  have p0002 := @g_fdmemex
  have p0003 := @g_cokex (syn_cfdprj0) (syn_cfdmem) p0001 p0002
  have p0004 := @g_fddomex A B hyp_fddomex_1 hyp_fddomex_2
  have p0005 :=
    @g_inex (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B) p0003 p0004
  have p0006 :=
    @g_eqeltri (syn_cfde0 A B)
      (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)) (syn_cvv) p0000
      p0005
  exact p0006

@[expose]
noncomputable def g_fde1ex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfde1 A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfde1 A B))
  have p0001 := @g_fdprj1ex
  have p0002 := @g_fdmemex
  have p0003 := @g_cokex (syn_cfdprj1) (syn_cfdmem) p0001 p0002
  have p0004 := @g_fddomex A B hyp_fddomex_1 hyp_fddomex_2
  have p0005 :=
    @g_inex (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B) p0003 p0004
  have p0006 :=
    @g_eqeltri (syn_cfde1 A B)
      (syn_cin (syn_ccomk (syn_cfdprj1) (syn_cfdmem)) (syn_cfddom A B)) (syn_cvv) p0000
      p0005
  exact p0006

@[expose]
noncomputable def g_fdsepex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdsep A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdsep A B))
  have p0001 := @g_fde0ex A B hyp_fddomex_1 hyp_fddomex_2
  have p0002 := @g_fde1ex A B hyp_fddomex_1 hyp_fddomex_2
  have p0003 := @g_symdifex (syn_cfde0 A B) (syn_cfde1 A B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cfdsep A B) (syn_csymdif (syn_cfde0 A B) (syn_cfde1 A B)) (syn_cvv)
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_fdliftex (R : Class)
    (hyp_fdliftex_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdlift R) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdlift R))
  have p0001 := @g_qkrelex R hyp_fdliftex_1
  have p0002 := @g_sikex (syn_cqkrel R) p0001
  have p0003 := @g_eqeltri (syn_cfdlift R) (syn_csik (syn_cqkrel R)) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_fdnonminex (A : Class) (B : Class) (R : Class)
    (hyp_fdnonminex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdnonminex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdnonminex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdnonmin R A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdnonmin R A B))
  have p0001 := @g_fdsepex A B hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0002 := @g_idex
  have p0003 := @g_difex R (syn_cid) hyp_fdnonminex_1 p0002
  have p0004 := @g_fdliftex (syn_cdif R (syn_cid)) p0003
  have p0005 := @g_cnvkex (syn_cfdlift (syn_cdif R (syn_cid))) p0004
  have p0006 :=
    @g_cokex (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))) p0001 p0005
  have p0007 :=
    @g_eqeltri (syn_cfdnonmin R A B)
      (syn_ccomk (syn_cfdsep A B) (syn_ccnvk (syn_cfdlift (syn_cdif R (syn_cid)))))
      (syn_cvv) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_fdminsepex (A : Class) (B : Class) (R : Class)
    (hyp_fdnonminex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_fdnonminex_2 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fdnonminex_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfdminsep R A B) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdminsep R A B))
  have p0001 := @g_fdsepex A B hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0002 := @g_fdnonminex A B R hyp_fdnonminex_1 hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0003 := @g_difex (syn_cfdsep A B) (syn_cfdnonmin R A B) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cfdminsep R A B) (syn_cdif (syn_cfdsep A B) (syn_cfdnonmin R A B))
      (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_fdliftval2 (x : Var) (R : Class) (e : Var) (c : Var) (d : Var)
    (dv_R_c : c ∉ R.fv) (dv_R_d : d ∉ R.fv) (_dv_R_e : e ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_c_d : c ≠ d) (dv_c_e : c ≠ e) (dv_c_x : c ≠ x) (dv_d_e : d ≠ e) (dv_d_x : d ≠ x)
    (_dv_e_x : e ≠ x) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R)) (syn_wex c
          (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
              (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))))) :=
  by
  have dv_cache_0001 : c ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_c_x,
          not_false_eq_true])
  have dv_cache_0002 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_x,
          not_false_eq_true])
  have dv_cache_0003 : c ∉ ((syn_csn (.cv e))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_c_e,
          not_false_eq_true])
  have dv_cache_0004 : d ∉ ((syn_csn (.cv e))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_d_e,
          not_false_eq_true])
  have dv_cache_0005 : c ∉ ((syn_cqkrel R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, dv_R_c,
          not_false_eq_true])
  have dv_cache_0006 : d ∉ ((syn_cqkrel R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cqkrel, dv_R_d,
          not_false_eq_true])
  have dv_cache_0007 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show c ≠ d from (by exact dv_c_d))
  have dv_cache_0008 : Disjoint (R).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (R).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((R).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (R).fv from (by exact dv_R_c))))))
  have dv_cache_0009 : Disjoint (R).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint (R).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((R).fv) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show d ∉ (R).fv from (by exact dv_R_d))))))
  have dv_cache_0010 : Disjoint ((Class.cv c)).fv ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv c)).fv ((Class.cv d)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (c),
            NFChoice.Compiler.CoreFVSimp.fv_class_cv (d)];
          exact
            (show Disjoint (({ c } : Finset Var)) (({ d } : Finset Var)) from
              (Finset.disjoint_singleton_left.mpr
                (show c ∉ ({ d } : Finset Var) from
                  (by
                    simpa only [Finset.mem_singleton] using
                      (show c ≠ d from (by exact dv_c_d))))))))
  have p0000 := (Nominal.classEqRefl (syn_cfdlift R))
  have p0001 :=
    @g_eleq2i (syn_cfdlift R) (syn_csik (syn_cqkrel R))
      (syn_copk (.cv x) (syn_csn (.cv e))) p0000
  have p0002 := @g_vex x
  have p0003 := @g_snex (.cv e)
  have p0004 :=
    @g_pm3_2i (.classMem (.cv x) (syn_cvv)) (.classMem (syn_csn (.cv e)) (syn_cvv)) p0002
      p0003
  have p0005 :=
    @g_opkelsikg c d (.cv x) (syn_csn (.cv e)) (syn_cqkrel R) (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_vex c
  have p0008 := @g_vex d
  have p0009 :=
    @g_qkrelbr R (.cv c) (.cv d) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0007 p0008
  have p0010 := (Nominal.biimpRefl (syn_wbr (.cv c) R (.cv d)))
  have p0011 :=
    @g_bicomi (syn_wbr (.cv c) R (.cv d)) (.classMem (syn_cop (.cv c) (.cv d)) R) p0010
  have p0012 :=
    @g_bitri (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R))
      (.classMem (syn_cop (.cv c) (.cv d)) R) (syn_wbr (.cv c) R (.cv d)) p0009 p0011
  have p0013 :=
    @g_n_3anbi3i (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R))
      (syn_wbr (.cv c) R (.cv d)) (.classEq (.cv x) (syn_csn (.cv c)))
      (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) p0012
  have p0014 :=
    @g_exbii
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
        (.classEq (syn_csn (.cv e)) (syn_csn (.cv d)))
        (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
        (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))
      d p0013
  have p0015 :=
    @g_exbii
      (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
          (.classEq (syn_csn (.cv e)) (syn_csn (.cv d)))
          (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R))))
      (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
          (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))))
      c p0014
  have p0016 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_csik (syn_cqkrel R)))
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (syn_csn (.cv e)) (syn_csn (.cv d)))
            (.classMem (syn_copk (.cv c) (.cv d)) (syn_cqkrel R)))))
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))))
      p0006 p0015
  have p0017 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R))
      (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_csik (syn_cqkrel R)))
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))))
      p0001 p0016
  exact p0017

@[expose]
noncomputable def g_fdliftval1 (x : Var) (R : Class) (e : Var) (c : Var)
    (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_c_e : c ≠ e)
    (dv_c_x : c ≠ x) (dv_e_x : e ≠ x) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R)) (syn_wex c
          (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ R.fv ∪ ({ e } : Finset Var) ∪ ({ c } : Finset Var)
  let d : Var := freshVar proofSupport 0
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_e : d ≠ e := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_d_ne_c : d ≠ c := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have dv_cache_0001 : c ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_c, not_false_eq_true])
  have dv_cache_0002 : d ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0003 : e ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_e, not_false_eq_true])
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
  have dv_cache_0005 : c ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0006 : c ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show c ≠ e from (by exact dv_c_e))
  have dv_cache_0007 : c ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show c ≠ x from (by exact dv_c_x))
  have dv_cache_0008 : d ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show d ≠ e from (by exact fresh_d_ne_e))
  have dv_cache_0009 : d ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0010 : e ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show e ≠ x from (by exact dv_e_x))
  have dv_cache_0011 : d ∉ ((Class.cv e)).fv :=
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
          fresh_d_ne_e, not_false_eq_true])
  have dv_cache_0012 :
    d ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_c, fresh_d_ne_e, fresh_d_not_R,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_fdliftval2 x R e c d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @g_vex e
  have p0002 := @g_sneqb (.cv e) (.cv d) p0001
  have p0003 := @g_eqcom (.cv e) (.cv d)
  have p0004 :=
    @g_bitri (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classEq (.cv e) (.cv d))
      (.classEq (.cv d) (.cv e)) p0002 p0003
  have p0005 :=
    @g_n_3anbi2i (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (.classEq (.cv d) (.cv e))
      (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)) p0004
  have p0006 :=
    @g_n_3ancoma (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv d) (.cv e))
      (syn_wbr (.cv c) R (.cv d))
  have p0007 :=
    @g_bitri
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
        (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c))) (.classEq (.cv d) (.cv e))
        (syn_wbr (.cv c) R (.cv d)))
      (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
        (syn_wbr (.cv c) R (.cv d)))
      p0005 p0006
  have p0008 :=
    @g_exbii
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
        (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))
      (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
        (syn_wbr (.cv c) R (.cv d)))
      d p0007
  have p0009 :=
    @g_exbii
      (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
          (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d))))
      (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wbr (.cv c) R (.cv d))))
      c p0008
  have p0010 :=
    @g_n_3anass (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
      (syn_wbr (.cv c) R (.cv d))
  have p0011 :=
    @g_exbii
      (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
        (syn_wbr (.cv c) R (.cv d)))
      (syn_wa (.classEq (.cv d) (.cv e))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d))))
      d p0010
  have p0013 := @g_breq2 (.cv d) (.cv e) (.cv c) R
  have p0014 :=
    @g_anbi2d (.classEq (.cv d) (.cv e)) (syn_wbr (.cv c) R (.cv d))
      (syn_wbr (.cv c) R (.cv e)) (.classEq (.cv x) (syn_csn (.cv c))) p0013
  have p0015 :=
    @g_ceqsexv (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))) d (.cv e)
      dv_cache_0011 dv_cache_0012 p0001 p0014
  have p0016 :=
    @g_bitri
      (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wbr (.cv c) R (.cv d))))
      (syn_wex d (syn_wa (.classEq (.cv d) (.cv e))
          (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv d)))))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))) p0011
      p0015
  have p0017 :=
    @g_exbii
      (syn_wex d (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
          (syn_wbr (.cv c) R (.cv d))))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))) c p0016
  have p0018 :=
    @g_bitri
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))))
      (syn_wex c (syn_wex d
          (syn_w3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (syn_csn (.cv c)))
            (syn_wbr (.cv c) R (.cv d)))))
      (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))))
      p0009 p0017
  have p0019 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_csn (.cv e))) (syn_cfdlift R))
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_csn (.cv c)))
            (.classEq (syn_csn (.cv e)) (syn_csn (.cv d))) (syn_wbr (.cv c) R (.cv d)))))
      (syn_wex c (syn_wa (.classEq (.cv x) (syn_csn (.cv c))) (syn_wbr (.cv c) R (.cv e))))
      p0000 p0018
  exact p0019

@[expose]
noncomputable def g_fdmemvalC (B : Class) (C : Class) (e : Var) :
    Nominal.NPrf
      (.imp (.classMem C B) (syn_wb
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
          (.classMem C (.cv e)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfdmem))
  have p0001 :=
    @g_eleq2i (syn_cfdmem) (syn_ccnvk (syn_csik (syn_cssetk)))
      (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) p0000
  have p0002 := @g_snex (.cv e)
  have p0003 := @g_snex (syn_csn C)
  have p0004 :=
    @g_opkelcnvk (syn_csn (.cv e)) (syn_csn (syn_csn C)) (syn_csik (syn_cssetk)) p0002
      p0003
  have p0005 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C)))
        (syn_ccnvk (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk)))
      p0001 p0004
  have p0006 := @g_snex C
  have p0007 := @g_vex e
  have p0008 := @g_opksnelsik (syn_csn C) (.cv e) (syn_cssetk) p0006 p0007
  have p0009 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (syn_csn C)) (syn_csn (.cv e))) (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) p0005 p0008
  have p0010 := @g_elex C B
  have p0012 := @g_a1i (.classMem (.cv e) (syn_cvv)) (.classMem C B) p0007
  have p0013 :=
    @g_jca (.classMem C B) (.classMem C (syn_cvv)) (.classMem (.cv e) (syn_cvv)) p0010
      p0012
  have p0014 := @g_elssetkg C (.cv e) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (.classMem C B) (syn_wa (.classMem C (syn_cvv)) (.classMem (.cv e) (syn_cvv)))
      (syn_wb (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) (.classMem C (.cv e)))
      p0013 p0014
  have p0016 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn C) (.cv e)) (syn_cssetk)) (.classMem C B)
      (.classMem C (.cv e)) p0009 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fdprj0valV (x : Var) (C : Class) (D : Class)
    (_dv_C_D : Disjoint C.fv D.fv) (_dv_C_x : x ∉ C.fv) (_dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
          (.classEq (.cv x) (syn_csn (syn_csn C))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ C.fv ∪ D.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
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
  have dv_cache_0003 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_a_not_C, fresh_a_not_D, or_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_b_not_C, fresh_b_not_D, or_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_c_not_C, fresh_c_not_D, or_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((syn_cidk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_cidk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((syn_cidk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0012 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0013 :
    a ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_a_not_C, fresh_a_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    b ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_b_not_C, fresh_b_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    c ∉ ((syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_c_not_C, fresh_c_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : c ∉ (D).fv :=
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
        simp only [fresh_c_not_D, not_false_eq_true])
  have dv_cache_0017 :
    c ∉
      ((syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a, fresh_c_ne_b, fresh_c_not_C,
          or_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ (C).fv :=
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
        simp only [fresh_b_not_C, not_false_eq_true])
  have dv_cache_0019 :
    b ∉
      ((syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0020 : a ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_C, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((Wff.classEq (.cv x) (syn_csn (syn_csn C)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_C, or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_cfdprj0))
  have p0001 :=
    @g_eleq2i (syn_cfdprj0) (syn_cins3k (syn_cidk)) (syn_copk (.cv x) (syn_copk C D))
      p0000
  have p0002 := @g_vex x
  have p0003 := @g_opkex C D
  have p0004 :=
    @g_opkelins3kg a b c (.cv x) (syn_copk C D) (syn_cidk) (syn_cvv) (syn_cvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0005 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (syn_copk C D) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cins3k (syn_cidk))) (syn_wex a
          (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
                (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)))))))
      p0002 p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cins3k (syn_cidk)))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
              (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk))))))
      p0001 p0005
  have p0007 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)) (syn_wex a (syn_wex b
            (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
                (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0006
  have p0008 := @g_biid (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
  have p0009 :=
    @g_a1i
      (syn_wb (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0008
  have p0010 := @g_vex c
  have p0011 := @g_opkthg C D (.cv b) (.cv c) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp3an3 (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
      (.classMem (.cv c) (syn_cvv))
      (syn_wb (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
        (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c))))
      p0010 p0011
  have p0013 := @g_eqcom C (.cv b)
  have p0014 := @g_eqcom D (.cv c)
  have p0015 :=
    @g_anbi12i (.classEq C (.cv b)) (.classEq (.cv b) C) (.classEq D (.cv c))
      (.classEq (.cv c) D) p0013 p0014
  have p0016 :=
    @g_a1i
      (syn_wb (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c)))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0015
  have p0017 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
      (syn_wa (.classEq C (.cv b)) (.classEq D (.cv c)))
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) p0012 p0016
  have p0018 := @g_vex a
  have p0019 := @g_vex b
  have p0020 := @g_opkelidkg (.cv a) (.cv b) (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (.cv b) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)) (.classEq (.cv a) (.cv b)))
      p0018 p0019 p0020
  have p0022 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0021
  have p0023 :=
    @g_n_3anbi123d (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D))
      (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)) (.classEq (.cv a) (.cv b)) p0009
      p0017 p0022
  have p0024 :=
    @g_n_3exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
        (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk)))
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0023
  have p0025 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (syn_copk C D) (syn_copk (.cv b) (.cv c)))
              (.classMem (syn_copk (.cv a) (.cv b)) (syn_cidk))))))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))))))
      p0007 p0024
  have p0026 :=
    @g_n_3anass (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))
  have p0027 :=
    @g_anass (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))
  have p0028 :=
    @g_anbi2i
      (syn_wa (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0027
  have p0029 :=
    @g_bitri
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b)))))
      p0026 p0028
  have p0030 :=
    @g_an12 (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))
  have p0031 :=
    @g_anbi2i
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))))
      (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0030
  have p0032 :=
    @g_bitri
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b)))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv c) D)
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      p0029 p0031
  have p0033 :=
    @g_an12 (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv c) D)
      (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))
  have p0034 :=
    @g_bitri
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (syn_wa (.classEq (.cv c) D)
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      p0032 p0033
  have p0035 :=
    @g_a1i
      (syn_wb (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
        (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0034
  have p0036 :=
    @g_n_3exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv c) D) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0035
  have p0037 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wex b (syn_wex c (syn_w3a (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))))))
      (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv c) D)
              (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))))
      p0025 p0036
  have p0038 := @g_simpr (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0039 :=
    @g_biidd (.classEq (.cv c) D)
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
  have p0040 :=
    @g_ceqsexgv
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      c D (syn_cvv) dv_cache_0016 dv_cache_0017 p0039
  have p0041 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem D (syn_cvv))
      (syn_wb (syn_wex c (syn_wa (.classEq (.cv c) D)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
        (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      p0038 p0040
  have p0042 :=
    @g_n_2exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wex c (syn_wa (.classEq (.cv c) D)
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      a b dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wex b (syn_wex c (syn_wa (.classEq (.cv c) D)
              (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
                (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      p0037 p0042
  have p0044 :=
    @g_an12 (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv b) C)
      (.classEq (.cv a) (.cv b))
  have p0045 :=
    @g_a1i
      (syn_wb (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0044
  have p0046 :=
    @g_n_2exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
        (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      (syn_wa (.classEq (.cv b) C) (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
          (.classEq (.cv a) (.cv b))))
      a b dv_cache_0013 dv_cache_0014 p0045
  have p0047 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
            (syn_wa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv b) C)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (.cv a) (.cv b))))))
      p0043 p0046
  have p0048 := @g_simpl (.classMem C (syn_cvv)) (.classMem D (syn_cvv))
  have p0049 := @g_eqeq2 (.cv b) C (.cv a)
  have p0050 :=
    @g_anbi2d (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)) (.classEq (.cv a) C)
      (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) p0049
  have p0051 :=
    @g_ceqsexgv
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)) b C
      (syn_cvv) dv_cache_0018 dv_cache_0019 p0050
  have p0052 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem C (syn_cvv))
      (syn_wb (syn_wex b (syn_wa (.classEq (.cv b) C)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))))
        (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)))
      p0048 p0051
  have p0053 :=
    @g_exbidv (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wex b (syn_wa (.classEq (.cv b) C)
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) (.cv b)))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)) a
      dv_cache_0013 p0052
  have p0054 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv b) C)
            (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
              (.classEq (.cv a) (.cv b))))))
      (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)))
      p0047 p0053
  have p0055 :=
    @g_ancom (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)
  have p0056 :=
    @g_exbii (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C))
      (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))) a p0055
  have p0057 :=
    @g_a1i
      (syn_wb (syn_wex a
          (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)))
        (syn_wex a
          (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))))))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv))) p0056
  have p0058 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wa (.classEq (.cv x) (syn_csn (syn_csn (.cv a)))) (.classEq (.cv a) C)))
      (syn_wex a (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))
      p0054 p0057
  have p0060 := @g_sneq (.cv a) C
  have p0061 := @g_sneqd (.classEq (.cv a) C) (syn_csn (.cv a)) (syn_csn C) p0060
  have p0062 :=
    @g_eqeq2d (.classEq (.cv a) C) (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn C))
      (.cv x) p0061
  have p0063 :=
    @g_ceqsexgv (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))
      (.classEq (.cv x) (syn_csn (syn_csn C))) a C (syn_cvv) dv_cache_0020 dv_cache_0021
      p0062
  have p0064 :=
    @g_syl (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem C (syn_cvv))
      (syn_wb (syn_wex a
          (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))
        (.classEq (.cv x) (syn_csn (syn_csn C))))
      p0048 p0063
  have p0065 :=
    @g_bitrd (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (syn_wex a (syn_wa (.classEq (.cv a) C) (.classEq (.cv x) (syn_csn (syn_csn (.cv a))))))
      (.classEq (.cv x) (syn_csn (syn_csn C))) p0058 p0064
  exact p0065

@[expose]
noncomputable def g_fde0valJp (A : Class) (B : Class) (C : Class) (D : Class) (e : Var)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (_dv_A_e : e ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_D : Disjoint B.fv D.fv) (_dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (_dv_C_e : e ∉ C.fv) (_dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem C B) (.classMem D B))
        (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
          (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({ e } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_x_ne_e : x ≠ e := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : x ∉ ((syn_csn (.cv e))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_e,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_copk C D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cfdprj0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cfdmem)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wa (.classMem C B) (.classMem D B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_x_not_C,
          fresh_x_not_B, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_csn (syn_csn C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_C,
          not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_e, fresh_x_not_C, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_cfde0 A B))
  have p0001 :=
    @g_eleq2i (syn_cfde0 A B)
      (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0001
  have p0003 :=
    @g_elin (syn_copk (syn_csn (.cv e)) (syn_copk C D))
      (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)
  have p0004 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B))) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
            (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
          (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_cin (syn_ccomk (syn_cfdprj0) (syn_cfdmem)) (syn_cfddom A B)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)))
      p0002 p0004
  have p0006 := @g_snex (.cv e)
  have p0007 := @g_opkex C D
  have p0008 :=
    @g_opkelcok x (syn_csn (.cv e)) (syn_copk C D) (syn_cfdprj0) (syn_cfdmem)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_ccomk (syn_cfdprj0) (syn_cfdmem))) (syn_wex x
          (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
            (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)))))
      (syn_wa (.classMem C B) (.classMem D B)) p0008
  have p0010 := @g_biid (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
  have p0011 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))
      (syn_wa (.classMem C B) (.classMem D B)) p0010
  have p0012 := @g_simpl (.classMem C B) (.classMem D B)
  have p0013 := @g_elex C B
  have p0014 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B)
      (.classMem C (syn_cvv)) p0012 p0013
  have p0015 := @g_simpr (.classMem C B) (.classMem D B)
  have p0016 := @g_elex D B
  have p0017 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem D B)
      (.classMem D (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem C B) (.classMem D B)) (.classMem C (syn_cvv))
      (.classMem D (syn_cvv)) p0014 p0017
  have p0019 := @g_fdprj0valV x C D dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0020 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wb (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
        (.classEq (.cv x) (syn_csn (syn_csn C))))
      p0018 p0019
  have p0021 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))
      (.classEq (.cv x) (syn_csn (syn_csn C))) p0011 p0020
  have p0022 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classEq (.cv x) (syn_csn (syn_csn C))))
      x dv_cache_0008 p0021
  have p0023 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classMem (syn_copk (.cv x) (syn_copk C D)) (syn_cfdprj0))))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classEq (.cv x) (syn_csn (syn_csn C)))))
      p0009 p0022
  have p0024 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classEq (.cv x) (syn_csn (syn_csn C)))
  have p0025 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classEq (.cv x) (syn_csn (syn_csn C))))
        (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C)))
          (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
      (syn_wa (.classMem C B) (.classMem D B)) p0024
  have p0026 :=
    @g_exbidv (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
        (.classEq (.cv x) (syn_csn (syn_csn C))))
      (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C)))
        (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem)))
      x dv_cache_0008 p0025
  have p0027 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
      (syn_wex x (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
          (.classEq (.cv x) (syn_csn (syn_csn C)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C)))
          (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
      p0023 p0026
  have p0028 := @g_snex (syn_csn C)
  have p0029 := @g_opkeq2 (.cv x) (syn_csn (syn_csn C)) (syn_csn (.cv e))
  have p0030 :=
    @g_eleq1d (.classEq (.cv x) (syn_csn (syn_csn C)))
      (syn_copk (syn_csn (.cv e)) (.cv x))
      (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem) p0029
  have p0031 :=
    @g_ceqsexgv (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) x
      (syn_csn (syn_csn C)) (syn_cvv) dv_cache_0009 dv_cache_0010 p0030
  have p0032 := Nominal.mp p0028 p0031
  have p0033 :=
    @g_a1i
      (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C)))
            (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)))
      (syn_wa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (syn_csn C)))
          (.classMem (syn_copk (syn_csn (.cv e)) (.cv x)) (syn_cfdmem))))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem)) p0027
      p0033
  have p0036 := @g_fdmemvalC B C e
  have p0037 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B)) (.classMem C B)
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
        (.classMem C (.cv e)))
      p0012 p0036
  have p0038 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_csn (syn_csn C))) (syn_cfdmem))
      (.classMem C (.cv e)) p0034 p0037
  have p0039 := (Nominal.classEqRefl (syn_cfddom A B))
  have p0040 :=
    @g_eleq2i (syn_cfddom A B) (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))
      (syn_copk (syn_csn (.cv e)) (syn_copk C D)) p0039
  have p0041 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cxpk (syn_cpw1 A) (syn_cxpk B B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0040
  have p0044 :=
    @g_opkelxpk (syn_csn (.cv e)) (syn_copk C D) (syn_cpw1 A) (syn_cxpk B B) p0006 p0007
  have p0045 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)))
        (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A))
          (.classMem (syn_copk C D) (syn_cxpk B B))))
      (syn_wa (.classMem C B) (.classMem D B)) p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_cxpk (syn_cpw1 A) (syn_cxpk B B)))
      (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A))
        (.classMem (syn_copk C D) (syn_cxpk B B)))
      p0041 p0045
  have p0047 := @g_snelpw1 (.cv e) A
  have p0048 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (.cv e) A))
      (syn_wa (.classMem C B) (.classMem D B)) p0047
  have p0056 := @g_opkelxpkg C D B B (syn_cvv) (syn_cvv)
  have p0057 :=
    @g_syl (syn_wa (.classMem C B) (.classMem D B))
      (syn_wa (.classMem C (syn_cvv)) (.classMem D (syn_cvv)))
      (syn_wb (.classMem (syn_copk C D) (syn_cxpk B B))
        (syn_wa (.classMem C B) (.classMem D B)))
      p0018 p0056
  have p0058 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_csn (.cv e)) (syn_cpw1 A)) (.classMem (.cv e) A)
      (.classMem (syn_copk C D) (syn_cxpk B B)) (syn_wa (.classMem C B) (.classMem D B))
      p0048 p0057
  have p0059 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (syn_wa (.classMem (syn_csn (.cv e)) (syn_cpw1 A))
        (.classMem (syn_copk C D) (syn_cxpk B B)))
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) p0046 p0058
  have p0060 := @g_iba (syn_wa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
  have p0061 :=
    @g_bicomd (syn_wa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B))) p0060
  have p0062 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (syn_wa (.classMem (.cv e) A) (syn_wa (.classMem C B) (.classMem D B)))
      (.classMem (.cv e) A) p0059 p0061
  have p0063 :=
    @g_anbi12d (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
        (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
      (.classMem C (.cv e))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B))
      (.classMem (.cv e) A) p0038 p0062
  have p0064 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D))
          (syn_ccomk (syn_cfdprj0) (syn_cfdmem)))
        (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfddom A B)))
      (syn_wa (.classMem C (.cv e)) (.classMem (.cv e) A)) p0005 p0063
  have p0065 := @g_ancom (.classMem C (.cv e)) (.classMem (.cv e) A)
  have p0066 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem C (.cv e)) (.classMem (.cv e) A))
        (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))))
      (syn_wa (.classMem C B) (.classMem D B)) p0065
  have p0067 :=
    @g_bitrd (syn_wa (.classMem C B) (.classMem D B))
      (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfde0 A B))
      (syn_wa (.classMem C (.cv e)) (.classMem (.cv e) A))
      (syn_wa (.classMem (.cv e) A) (.classMem C (.cv e))) p0064 p0066
  exact p0067


end NFChoice.DirectNominalPrf.WPPReplay

end
