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

/-- Checked nominal proof certificate identified upstream as `g_frec0`. -/
@[expose]
noncomputable def gFrec0 (ph : Wff) (F : Class) (G : Class) (I : Class)
    (hyp_frec0_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_frec0_2 : Nominal.NPrf (.imp ph (.classMem G (synCfuns))))
    (hyp_frec0_3 : Nominal.NPrf (.imp ph (.classMem I (synCdm G))))
    (hyp_frec0_4 : Nominal.NPrf (.imp ph (synWss (synCrn G) (synCdm G)))) :
    Nominal.NPrf (.imp ph (.classEq (synCfv F (synC0c)) I)) :=
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
  have dv_cache_0003 : y ∉ ((synCop (synC0c) I)).fv :=
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
    y ∉ ((synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)).fv :=
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
  have dv_cache_0006 : y ∉ ((synCsn (synCop (synC0c) I))).fv :=
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
  have p0000 := @gPeano1
  have p0001 := @gOpexg (synC0c) I (synCnnc) (synCdm G)
  have p0002 :=
    @gSylancr ph (.classMem (synC0c) (synCnnc)) (.classMem I (synCdm G))
      (.classMem (synCop (synC0c) I) (synCvv)) p0000 hyp_frec0_3 p0001
  have p0003 := @gSnidg (synCop (synC0c) I) (synCvv)
  have p0004 :=
    @gSyl ph (.classMem (synCop (synC0c) I) (synCvv))
      (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I))) p0002 p0003
  have p0005 :=
    @gOrcd ph (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I)))
      (synWrex y F (synWbr (.cv y)
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
          (synCop (synC0c) I)))
      p0004
  have p0006 := @gSnex (synCop (synC0c) I)
  have p0007 := @gCsucex x
  have p0008 :=
    @gPprodexg (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G (synCvv)
      (synCfuns)
  have p0009 :=
    @gSylancr ph
      (.classMem (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (synCvv))
      (.classMem G (synCfuns))
      (.classMem (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) (synCvv))
      p0007 hyp_frec0_2 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec x G I
      dv_cache_0001 dv_cache_0002
  have p0011 :=
    @gEqtri F (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      hyp_frec0_1 p0010
  have p0012 :=
    @gClos1basesucg y (synCop (synC0c) I) F
      (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 p0011
  have p0013 :=
    @gSylancr ph (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G) (synCvv))
      (synWb (.classMem (synCop (synC0c) I) F)
        (synWo (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I))) (synWrex y F
            (synWbr (.cv y) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
              (synCop (synC0c) I)))))
      p0006 p0009 p0012
  have p0014 :=
    @gMpbird ph (.classMem (synCop (synC0c) I) F)
      (synWo (.classMem (synCop (synC0c) I) (synCsn (synCop (synC0c) I))) (synWrex y F
          (synWbr (.cv y) (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
            (synCop (synC0c) I))))
      p0005 p0013
  have p0015 := @gFnfrec ph F G I hyp_frec0_1 hyp_frec0_2 hyp_frec0_3 hyp_frec0_4
  have p0017 := @gFnopfvb (synCnnc) (synC0c) I F
  have p0018 :=
    @gSylancl ph (synWfn F (synCnnc)) (.classMem (synC0c) (synCnnc))
      (synWb (.classEq (synCfv F (synC0c)) I) (.classMem (synCop (synC0c) I) F))
      p0015 p0000 p0017
  have p0019 :=
    @gMpbird ph (.classEq (synCfv F (synC0c)) I) (.classMem (synCop (synC0c) I) F)
      p0014 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_frecsuc`. -/
@[expose]
noncomputable def gFrecsuc (ph : Wff) (F : Class) (G : Class) (I : Class) (X : Class)
    (hyp_frecsuc_1 : Nominal.NPrf (.classEq F (synCfrec G I)))
    (hyp_frecsuc_2 : Nominal.NPrf (.imp ph (.classMem G (synCfuns))))
    (hyp_frecsuc_3 : Nominal.NPrf (.imp ph (.classMem I (synCdm G))))
    (hyp_frecsuc_4 : Nominal.NPrf (.imp ph (synWss (synCrn G) (synCdm G))))
    (hyp_frecsuc_5 : Nominal.NPrf (.imp ph (.classMem X (synCnnc)))) :
    Nominal.NPrf
      (.imp ph (.classEq (synCfv F (synCplc X (synC1c))) (synCfv G (synCfv F X)))) :=
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
  have dv_cache_0001 : y ∉ ((synCplc (.cv w) (synC1c))).fv := by
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
  have dv_cache_0005 : w ∉ ((synCplc X (synC1c))).fv :=
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
  have dv_cache_0006 : y ∉ ((synCplc X (synC1c))).fv :=
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
    w ∉ ((Wff.classEq (synCplc X (synC1c)) (synCplc X (synC1c)))).fv :=
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
    y ∉ ((Wff.classEq (synCplc X (synC1c)) (synCplc X (synC1c)))).fv :=
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
  have dv_cache_0009 : y ∉ ((synCop X (synCfv F X))).fv :=
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
      ((synWa (synWbr X (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
            (synCplc X (synC1c))) (synWbr (synCfv F X) G (synCfv G (synCfv F X))))).fv :=
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
    y ∉ ((synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))).fv :=
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
    y ∉ ((synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)).fv :=
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
  have dv_cache_0016 : y ∉ ((synCsn (synCop (synC0c) I))).fv :=
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
  have p0000 := @gFnfrec ph F G I hyp_frecsuc_1 hyp_frecsuc_2 hyp_frecsuc_3 hyp_frecsuc_4
  have p0001 := @gFnfun (synCnnc) F
  have p0002 := @gSyl ph (synWfn F (synCnnc)) (synWfun F) p0000 p0001
  have p0003 :=
    @gDmfrec ph F G I (synCfuns) hyp_frecsuc_1 hyp_frecsuc_2 hyp_frecsuc_3 hyp_frecsuc_4
  have p0004 := @gEleqtrrd ph X (synCnnc) (synCdm F) hyp_frecsuc_5 p0003
  have p0005 := @gFunfvop X F
  have p0006 :=
    @gSyl2anc ph (synWfun F) (.classMem X (synCdm F))
      (.classMem (synCop X (synCfv F X)) F) p0002 p0004 p0005
  have p0007 := @gEqid (synCplc X (synC1c))
  have p0008 := @gPeano2 X
  have p0009 :=
    @gSyl ph (.classMem X (synCnnc)) (.classMem (synCplc X (synC1c)) (synCnnc))
      hyp_frecsuc_5 p0008
  have p0010 := @gAddceq1 (.cv w) X (synC1c)
  have p0011 :=
    @gEqeq2d (.classEq (.cv w) X) (synCplc (.cv w) (synC1c)) (synCplc X (synC1c))
      (.cv y) p0010
  have p0012 := @gEqeq1 (.cv y) (synCplc X (synC1c)) (synCplc X (synC1c))
  have p0013 := @gMptv w y (synCplc (.cv w) (synC1c)) dv_cache_0001 dv_cache_0002
  have p0014 :=
    @gBrabg (.classEq (.cv y) (synCplc (.cv w) (synC1c)))
      (.classEq (.cv y) (synCplc X (synC1c)))
      (.classEq (synCplc X (synC1c)) (synCplc X (synC1c))) w y X
      (synCplc X (synC1c)) (synCnnc) (synCnnc)
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0002 p0011 p0012
      p0013
  have p0015 :=
    @gSyl2anc ph (.classMem X (synCnnc)) (.classMem (synCplc X (synC1c)) (synCnnc))
      (synWb (synWbr X (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synCplc X (synC1c))) (.classEq (synCplc X (synC1c)) (synCplc X (synC1c))))
      hyp_frecsuc_5 p0009 p0014
  have p0016 :=
    @gMpbiri ph
      (synWbr X (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCplc X (synC1c)))
      (.classEq (synCplc X (synC1c)) (synCplc X (synC1c))) p0007 p0015
  have p0017 := @gElfunsi G
  have p0018 := @gSyl ph (.classMem G (synCfuns)) (synWfun G) hyp_frecsuc_2 p0017
  have p0019 := @gSnssd ph I (synCdm G) hyp_frecsuc_3
  have p0020 := @gUnssd ph (synCrn G) (synCsn I) (synCdm G) hyp_frecsuc_4 p0019
  have p0021 := @gFrecxpg F G I (synCfuns) hyp_frecsuc_1
  have p0022 :=
    @gSyl ph (.classMem G (synCfuns))
      (synWss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))) hyp_frecsuc_2
      p0021
  have p0023 := @gRnss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))
  have p0024 :=
    @gSyl ph (synWss F (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))
      (synWss (synCrn F) (synCrn (synCxp (synCnnc) (synCun (synCrn G) (synCsn I)))))
      p0022 p0023
  have p0025 := @gRnxpss (synCnnc) (synCun (synCrn G) (synCsn I))
  have p0026 :=
    @gSyl6ss ph (synCrn F)
      (synCrn (synCxp (synCnnc) (synCun (synCrn G) (synCsn I))))
      (synCun (synCrn G) (synCsn I)) p0024 p0025
  have p0027 := @gFvelrn X F
  have p0028 :=
    @gSyl2anc ph (synWfun F) (.classMem X (synCdm F))
      (.classMem (synCfv F X) (synCrn F)) p0002 p0004 p0027
  have p0029 :=
    @gSseldd ph (synCrn F) (synCun (synCrn G) (synCsn I)) (synCfv F X) p0026 p0028
  have p0030 :=
    @gSseldd ph (synCun (synCrn G) (synCsn I)) (synCdm G) (synCfv F X) p0020 p0029
  have p0031 := @gFunfvop (synCfv F X) G
  have p0032 :=
    @gSyl2anc ph (synWfun G) (.classMem (synCfv F X) (synCdm G))
      (.classMem (synCop (synCfv F X) (synCfv G (synCfv F X))) G) p0018 p0030 p0031
  have p0033 := (Nominal.biimpRefl (synWbr (synCfv F X) G (synCfv G (synCfv F X))))
  have p0034 :=
    @gSylibr ph (.classMem (synCop (synCfv F X) (synCfv G (synCfv F X))) G)
      (synWbr (synCfv F X) G (synCfv G (synCfv F X))) p0032 p0033
  have p0035 :=
    @gBreq1 (.cv y) (synCop X (synCfv F X))
      (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
  have p0036 :=
    @gQrpprod X (synCfv F X) (synCplc X (synC1c)) (synCfv G (synCfv F X))
      (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G
  have p0037 :=
    @gSyl6bb (.classEq (.cv y) (synCop X (synCfv F X)))
      (synWbr (.cv y) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))))
      (synWbr (synCop X (synCfv F X))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))))
      (synWa (synWbr X (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synCplc X (synC1c))) (synWbr (synCfv F X) G (synCfv G (synCfv F X))))
      p0035 p0036
  have p0038 :=
    @gRspcev
      (synWbr (.cv y) (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
        (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))))
      (synWa (synWbr X (synCmpt w (synCvv) (synCplc (.cv w) (synC1c)))
          (synCplc X (synC1c))) (synWbr (synCfv F X) G (synCfv G (synCfv F X))))
      y (synCop X (synCfv F X)) F dv_cache_0009 dv_cache_0010 dv_cache_0011 p0037
  have p0039 :=
    @gSyl12anc ph (.classMem (synCop X (synCfv F X)) F)
      (synWbr X (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCplc X (synC1c)))
      (synWbr (synCfv F X) G (synCfv G (synCfv F X)))
      (synWrex y F (synWbr (.cv y)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))))
      p0006 p0016 p0034 p0038
  have p0040 :=
    @gOlcd ph
      (synWrex y F (synWbr (.cv y)
          (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
          (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))))
      (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))
        (synCsn (synCop (synC0c) I)))
      p0039
  have p0041 := @gSnex (synCop (synC0c) I)
  have p0042 := @gCsucex w
  have p0043 :=
    @gPprodexg (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G (synCvv)
      (synCfuns)
  have p0044 :=
    @gSylancr ph
      (.classMem (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) (synCvv))
      (.classMem G (synCfuns))
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      p0042 hyp_frecsuc_2 p0043
  have p0045 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec w G I
      dv_cache_0012 dv_cache_0013
  have p0046 :=
    @gEqtri F (synCfrec G I)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G))
      hyp_frecsuc_1 p0045
  have p0047 :=
    @gClos1basesucg y (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))) F
      (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
      (synCsn (synCop (synC0c) I)) (synCvv) (synCvv) dv_cache_0014 dv_cache_0010
      dv_cache_0015 dv_cache_0016 p0046
  have p0048 :=
    @gSylancr ph (.classMem (synCsn (synCop (synC0c) I)) (synCvv))
      (.classMem (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G) (synCvv))
      (synWb (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))) F) (synWo
          (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))
            (synCsn (synCop (synC0c) I))) (synWrex y F (synWbr (.cv y)
              (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
              (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))))))
      p0041 p0044 p0047
  have p0049 :=
    @gMpbird ph (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))) F)
      (synWo (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X)))
          (synCsn (synCop (synC0c) I))) (synWrex y F (synWbr (.cv y)
            (synCpprod (synCmpt w (synCvv) (synCplc (.cv w) (synC1c))) G)
            (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))))))
      p0040 p0048
  have p0050 := @gFnopfvb (synCnnc) (synCplc X (synC1c)) (synCfv G (synCfv F X)) F
  have p0051 :=
    @gSyl2anc ph (synWfn F (synCnnc)) (.classMem (synCplc X (synC1c)) (synCnnc))
      (synWb (.classEq (synCfv F (synCplc X (synC1c))) (synCfv G (synCfv F X)))
        (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))) F))
      p0000 p0009 p0050
  have p0052 :=
    @gMpbird ph (.classEq (synCfv F (synCplc X (synC1c))) (synCfv G (synCfv F X)))
      (.classMem (synCop (synCplc X (synC1c)) (synCfv G (synCfv F X))) F) p0049 p0051
  exact p0052

/-- Checked nominal proof certificate identified upstream as `g_wppcg`. -/
@[expose]
noncomputable def gWppcg (A : Class) (B : Class) (f : Var) (g : Var) (h : Var)
    (V : Class) (W : Class) (_dv_A_V : Disjoint A.fv V.fv) (_dv_A_W : Disjoint A.fv W.fv)
    (dv_A_f : f ∉ A.fv) (dv_A_g : g ∉ A.fv) (dv_A_h : h ∉ A.fv)
    (_dv_B_V : Disjoint B.fv V.fv) (_dv_B_W : Disjoint B.fv W.fv) (dv_B_f : f ∉ B.fv)
    (dv_B_g : g ∉ B.fv) (dv_B_h : h ∉ B.fv) (_dv_V_W : Disjoint V.fv W.fv)
    (dv_f_g : f ≠ g) (dv_f_h : f ≠ h) (dv_g_h : g ≠ h) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.imp (synWwpp) (.imp
            (synWa (synWex f (synWfo (.cv f) B A)) (synWex g (synWf1 (.cv g) B A)))
            (synWex h (synWf1 (.cv h) A B))))) :=
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
  have dv_cache_0011 : f ∉ ((synWa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv :=
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
  have dv_cache_0012 : g ∉ ((synWa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv :=
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
  have dv_cache_0013 : h ∉ ((synWa (.classEq (.cv x) A) (.classEq (.cv y) B))).fv :=
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
      ((Wff.imp (synWa (synWex f (synWfo (.cv f) B A)) (synWex g (synWf1 (.cv g) B A)))
          (synWex h (synWf1 (.cv h) A B)))).fv :=
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
      ((Wff.imp (synWa (synWex f (synWfo (.cv f) B A)) (synWex g (synWf1 (.cv g) B A)))
          (synWex h (synWf1 (.cv h) A B)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfWpp x y f g h
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @gBiimpi (synWwpp)
      (.all x (.all y (.imp (synWa (synWex f (synWfo (.cv f) (.cv y) (.cv x)))
              (synWex g (synWf1 (.cv g) (.cv y) (.cv x))))
            (synWex h (synWf1 (.cv h) (.cv x) (.cv y))))))
      p0000
  have p0002 := @gFoeq3 (.cv x) A (.cv y) (.cv f)
  have p0003 := @gFoeq2 (.cv y) B A (.cv f)
  have p0004 :=
    @gSylan9bb (.classEq (.cv x) A) (synWfo (.cv f) (.cv y) (.cv x))
      (synWfo (.cv f) (.cv y) A) (.classEq (.cv y) B) (synWfo (.cv f) B A) p0002 p0003
  have p0005 :=
    @gExbidv (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWfo (.cv f) (.cv y) (.cv x)) (synWfo (.cv f) B A) f dv_cache_0011 p0004
  have p0006 := @gF1eq3 (.cv x) A (.cv y) (.cv g)
  have p0007 := @gF1eq2 (.cv y) B A (.cv g)
  have p0008 :=
    @gSylan9bb (.classEq (.cv x) A) (synWf1 (.cv g) (.cv y) (.cv x))
      (synWf1 (.cv g) (.cv y) A) (.classEq (.cv y) B) (synWf1 (.cv g) B A) p0006 p0007
  have p0009 :=
    @gExbidv (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWf1 (.cv g) (.cv y) (.cv x)) (synWf1 (.cv g) B A) g dv_cache_0012 p0008
  have p0010 :=
    @gAnbi12d (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWex f (synWfo (.cv f) (.cv y) (.cv x))) (synWex f (synWfo (.cv f) B A))
      (synWex g (synWf1 (.cv g) (.cv y) (.cv x))) (synWex g (synWf1 (.cv g) B A))
      p0005 p0009
  have p0011 := @gF1eq2 (.cv x) A (.cv y) (.cv h)
  have p0012 := @gF1eq3 (.cv y) B A (.cv h)
  have p0013 :=
    @gSylan9bb (.classEq (.cv x) A) (synWf1 (.cv h) (.cv x) (.cv y))
      (synWf1 (.cv h) A (.cv y)) (.classEq (.cv y) B) (synWf1 (.cv h) A B) p0011 p0012
  have p0014 :=
    @gExbidv (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWf1 (.cv h) (.cv x) (.cv y)) (synWf1 (.cv h) A B) h dv_cache_0013 p0013
  have p0015 :=
    @gImbi12d (synWa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (synWa (synWex f (synWfo (.cv f) (.cv y) (.cv x)))
        (synWex g (synWf1 (.cv g) (.cv y) (.cv x))))
      (synWa (synWex f (synWfo (.cv f) B A)) (synWex g (synWf1 (.cv g) B A)))
      (synWex h (synWf1 (.cv h) (.cv x) (.cv y))) (synWex h (synWf1 (.cv h) A B))
      p0010 p0014
  have p0016 :=
    @gSpc2gv
      (.imp (synWa (synWex f (synWfo (.cv f) (.cv y) (.cv x)))
          (synWex g (synWf1 (.cv g) (.cv y) (.cv x))))
        (synWex h (synWf1 (.cv h) (.cv x) (.cv y))))
      (.imp (synWa (synWex f (synWfo (.cv f) B A)) (synWex g (synWf1 (.cv g) B A)))
        (synWex h (synWf1 (.cv h) A B)))
      x y A B V W dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0010 p0015
  have p0017 :=
    @gSyl5 (synWwpp)
      (.all x (.all y (.imp (synWa (synWex f (synWfo (.cv f) (.cv y) (.cv x)))
              (synWex g (synWf1 (.cv g) (.cv y) (.cv x))))
            (synWex h (synWf1 (.cv h) (.cv x) (.cv y))))))
      (synWa (.classMem A V) (.classMem B W))
      (.imp (synWa (synWex f (synWfo (.cv f) B A)) (synWex g (synWf1 (.cv g) B A)))
        (synWex h (synWf1 (.cv h) A B)))
      p0001 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_nnnzdf`. -/
@[expose]
noncomputable def gNnnzdf (y : Var) :
    Nominal.NPrf
      (.classEq (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
        (synCdif (synCnnc) (synCsn (synC0c)))) :=
  by
  have dv_cache_0001 : y ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC0c)).fv :=
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
  have p0000 := @gNotrab (.classEq (.cv y) (synC0c)) y (synCnnc) dv_cache_0001
  have p0001 := @gPeano1
  have p0002 := @gRabsn y (synCnnc) (synC0c) dv_cache_0001 dv_cache_0002
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gDifeq2i (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))) (synCsn (synC0c))
      (synCnnc) p0003
  have p0005 :=
    @gEqtr3i (synCdif (synCnnc) (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nnnzex`. -/
@[expose]
noncomputable def gNnnzex (y : Var) :
    Nominal.NPrf
      (.classMem (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) (synCvv)) :=
  by
  have dv_cache_0001 : y ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC0c)).fv :=
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
  have p0000 := @gNotrab (.classEq (.cv y) (synC0c)) y (synCnnc) dv_cache_0001
  have p0001 := @gPeano1
  have p0002 := @gRabsn y (synCnnc) (synC0c) dv_cache_0001 dv_cache_0002
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gDifeq2i (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))) (synCsn (synC0c))
      (synCnnc) p0003
  have p0005 :=
    @gEqtr3i (synCdif (synCnnc) (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0000 p0004
  have p0006 := @gNncex
  have p0007 := @gSnex (synC0c)
  have p0008 := @gDifex (synCnnc) (synCsn (synC0c)) p0006 p0007
  have p0009 :=
    @gEqeltri (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) (synCvv) p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_fopprod`. -/
@[expose]
noncomputable def gFopprod (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfo F A C) (synWfo G B D))
        (synWfo (synCpprod F G) (synCxp A B) (synCxp C D))) :=
  by
  have p0000 := @gSimpl (synWfo F A C) (synWfo G B D)
  have p0001 := @gFofn A C F
  have p0002 :=
    @gSyl (synWa (synWfo F A C) (synWfo G B D)) (synWfo F A C) (synWfn F A) p0000
      p0001
  have p0003 := @gSimpr (synWfo F A C) (synWfo G B D)
  have p0004 := @gFofn B D G
  have p0005 :=
    @gSyl (synWa (synWfo F A C) (synWfo G B D)) (synWfo G B D) (synWfn G B) p0003
      p0004
  have p0006 :=
    @gJca (synWa (synWfo F A C) (synWfo G B D)) (synWfn F A) (synWfn G B) p0002
      p0005
  have p0007 := @gFnpprod A B F G
  have p0008 :=
    @gSyl (synWa (synWfo F A C) (synWfo G B D)) (synWa (synWfn F A) (synWfn G B))
      (synWfn (synCpprod F G) (synCxp A B)) p0006 p0007
  have p0009 := @gRnpprod F G
  have p0010 :=
    @gA1i (.classEq (synCrn (synCpprod F G)) (synCxp (synCrn F) (synCrn G)))
      (synWa (synWfo F A C) (synWfo G B D)) p0009
  have p0012 := @gForn A C F
  have p0013 :=
    @gSyl (synWa (synWfo F A C) (synWfo G B D)) (synWfo F A C)
      (.classEq (synCrn F) C) p0000 p0012
  have p0015 := @gForn B D G
  have p0016 :=
    @gSyl (synWa (synWfo F A C) (synWfo G B D)) (synWfo G B D)
      (.classEq (synCrn G) D) p0003 p0015
  have p0017 :=
    @gXpeq12d (synWa (synWfo F A C) (synWfo G B D)) (synCrn F) C (synCrn G) D p0013
      p0016
  have p0018 :=
    @gEqtrd (synWa (synWfo F A C) (synWfo G B D)) (synCrn (synCpprod F G))
      (synCxp (synCrn F) (synCrn G)) (synCxp C D) p0010 p0017
  have p0019 :=
    @gJca (synWa (synWfo F A C) (synWfo G B D))
      (synWfn (synCpprod F G) (synCxp A B))
      (.classEq (synCrn (synCpprod F G)) (synCxp C D)) p0008 p0018
  have p0020 := (Nominal.biimpRefl (synWfo (synCpprod F G) (synCxp A B) (synCxp C D)))
  have p0021 :=
    @gA1i
      (synWb (synWfo (synCpprod F G) (synCxp A B) (synCxp C D))
        (synWa (synWfn (synCpprod F G) (synCxp A B))
          (.classEq (synCrn (synCpprod F G)) (synCxp C D))))
      (synWa (synWfo F A C) (synWfo G B D)) p0020
  have p0022 :=
    @gMpbird (synWa (synWfo F A C) (synWfo G B D))
      (synWfo (synCpprod F G) (synCxp A B) (synCxp C D))
      (synWa (synWfn (synCpprod F G) (synCxp A B))
        (.classEq (synCrn (synCpprod F G)) (synCxp C D)))
      p0019 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_foun`. -/
@[expose]
noncomputable def gFoun (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
        (synWfo (synCun F G) (synCun A B) (synCun C D))) :=
  by
  have p0000 :=
    @gSimpl (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0))
  have p0001 := @gSimpl (synWfo F A C) (synWfo G B D)
  have p0002 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWa (synWfo F A C) (synWfo G B D)) (synWfo F A C) p0000 p0001
  have p0003 := @gFofn A C F
  have p0004 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfo F A C) (synWfn F A) p0002 p0003
  have p0006 := @gSimpr (synWfo F A C) (synWfo G B D)
  have p0007 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWa (synWfo F A C) (synWfo G B D)) (synWfo G B D) p0000 p0006
  have p0008 := @gFofn B D G
  have p0009 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfo G B D) (synWfn G B) p0007 p0008
  have p0010 :=
    @gJca
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfn F A) (synWfn G B) p0004 p0009
  have p0011 :=
    @gSimpr (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0))
  have p0012 :=
    @gJca
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWa (synWfn F A) (synWfn G B)) (.classEq (synCin A B) (synC0)) p0010 p0011
  have p0013 := @gFnun A B F G
  have p0014 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWa (synWa (synWfn F A) (synWfn G B)) (.classEq (synCin A B) (synC0)))
      (synWfn (synCun F G) (synCun A B)) p0012 p0013
  have p0015 := @gRnun F G
  have p0016 :=
    @gA1i (.classEq (synCrn (synCun F G)) (synCun (synCrn F) (synCrn G)))
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      p0015
  have p0020 := @gForn A C F
  have p0021 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfo F A C) (.classEq (synCrn F) C) p0002 p0020
  have p0025 := @gForn B D G
  have p0026 :=
    @gSyl
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfo G B D) (.classEq (synCrn G) D) p0007 p0025
  have p0027 :=
    @gUneq12d
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synCrn F) C (synCrn G) D p0021 p0026
  have p0028 :=
    @gEqtrd
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synCrn (synCun F G)) (synCun (synCrn F) (synCrn G)) (synCun C D) p0016 p0027
  have p0029 :=
    @gJca
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfn (synCun F G) (synCun A B))
      (.classEq (synCrn (synCun F G)) (synCun C D)) p0014 p0028
  have p0030 := (Nominal.biimpRefl (synWfo (synCun F G) (synCun A B) (synCun C D)))
  have p0031 :=
    @gA1i
      (synWb (synWfo (synCun F G) (synCun A B) (synCun C D))
        (synWa (synWfn (synCun F G) (synCun A B))
          (.classEq (synCrn (synCun F G)) (synCun C D))))
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      p0030
  have p0032 :=
    @gMpbird
      (synWa (synWa (synWfo F A C) (synWfo G B D)) (.classEq (synCin A B) (synC0)))
      (synWfo (synCun F G) (synCun A B) (synCun C D))
      (synWa (synWfn (synCun F G) (synCun A B))
        (.classEq (synCrn (synCun F G)) (synCun C D)))
      p0029 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_xnnex`. -/
@[expose]
noncomputable def gXnnex (x : Var) :
    Nominal.NPrf (.classMem (synCxp (.cv x) (synCnnc)) (synCvv)) :=
  by
  have p0000 := @gVex x
  have p0001 := @gNncex
  have p0002 := @gXpex (.cv x) (synCnnc) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_padsetex`. -/
@[expose]
noncomputable def gPadsetex (x : Var) (y : Var) (v : Var) (_dv_v_x : v ≠ x)
    (_dv_v_y : v ≠ y) (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCvv)) :=
  by
  have dv_cache_0001 : y ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC0c)).fv :=
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
  have p0000 := @gVex v
  have p0001 := @gSnex (synC0c)
  have p0002 := @gXpex (.cv v) (synCsn (synC0c)) p0000 p0001
  have p0003 := @gVex x
  have p0004 := @gNotrab (.classEq (.cv y) (synC0c)) y (synCnnc) dv_cache_0001
  have p0005 := @gPeano1
  have p0006 := @gRabsn y (synCnnc) (synC0c) dv_cache_0001 dv_cache_0002
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gDifeq2i (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))) (synCsn (synC0c))
      (synCnnc) p0007
  have p0009 :=
    @gEqtr3i (synCdif (synCnnc) (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0004 p0008
  have p0010 := @gNncex
  have p0012 := @gDifex (synCnnc) (synCsn (synC0c)) p0010 p0001
  have p0013 :=
    @gEqeltri (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) (synCvv) p0009 p0012
  have p0014 :=
    @gXpex (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) p0003
      p0013
  have p0015 :=
    @gUnex (synCxp (.cv v) (synCsn (synC0c)))
      (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))) p0002
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

/-- Checked nominal proof certificate identified upstream as `g_xnndisj`. -/
@[expose]
noncomputable def gXnndisj (y : Var) (X : Class) (_dv_X_y : y ∉ X.fv) :
    Nominal.NPrf
      (.classEq (synCin (synCxp X (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))) (synC0)) :=
  by
  have dv_cache_0001 : y ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC0c)).fv :=
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
  have p0000 := @gDisjdif (synCsn (synC0c)) (synCnnc)
  have p0001 :=
    @gXpdisj2 (synCsn (synC0c)) (synCdif (synCnnc) (synCsn (synC0c))) X X
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gNotrab (.classEq (.cv y) (synC0c)) y (synCnnc) dv_cache_0001
  have p0004 := @gPeano1
  have p0005 := @gRabsn y (synCnnc) (synC0c) dv_cache_0001 dv_cache_0002
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gDifeq2i (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))) (synCsn (synC0c))
      (synCnnc) p0006
  have p0008 :=
    @gEqtr3i (synCdif (synCnnc) (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0003 p0007
  have p0009 :=
    @gEqcomi (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0008
  have p0010 :=
    @gXpeq2i (synCdif (synCnnc) (synCsn (synC0c)))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) X p0009
  have p0011 :=
    @gIneq2i (synCxp X (synCdif (synCnnc) (synCsn (synC0c))))
      (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCxp X (synCsn (synC0c))) p0010
  have p0012 :=
    @gEqtr3i
      (synCin (synCxp X (synCsn (synC0c)))
        (synCxp X (synCdif (synCnnc) (synCsn (synC0c)))))
      (synC0)
      (synCin (synCxp X (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      p0002 p0011
  have p0013 :=
    @gEqcomi (synC0)
      (synCin (synCxp X (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_xnnun`. -/
@[expose]
noncomputable def gXnnun (y : Var) (X : Class) (_dv_X_y : y ∉ X.fv) :
    Nominal.NPrf
      (.classEq (synCun (synCxp X (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCxp X (synCnnc))) :=
  by
  have dv_cache_0001 : y ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC0c)).fv :=
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
  have p0000 := @gUndif2 (synCsn (synC0c)) (synCnnc)
  have p0001 := @gPeano1
  have p0002 := @gSnssi (synC0c) (synCnnc)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gSsequn1 (synCsn (synC0c)) (synCnnc)
  have p0005 :=
    @gMpbi (synWss (synCsn (synC0c)) (synCnnc))
      (.classEq (synCun (synCsn (synC0c)) (synCnnc)) (synCnnc)) p0003 p0004
  have p0006 :=
    @gEqtri (synCun (synCsn (synC0c)) (synCdif (synCnnc) (synCsn (synC0c))))
      (synCun (synCsn (synC0c)) (synCnnc)) (synCnnc) p0000 p0005
  have p0007 := @gNotrab (.classEq (.cv y) (synC0c)) y (synCnnc) dv_cache_0001
  have p0009 := @gRabsn y (synCnnc) (synC0c) dv_cache_0001 dv_cache_0002
  have p0010 := Nominal.mp p0001 p0009
  have p0011 :=
    @gDifeq2i (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))) (synCsn (synC0c))
      (synCnnc) p0010
  have p0012 :=
    @gEqtr3i (synCdif (synCnnc) (synCrab y (synCnnc) (.classEq (.cv y) (synC0c))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0007 p0011
  have p0013 :=
    @gEqcomi (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) p0012
  have p0014 :=
    @gUneq2i (synCdif (synCnnc) (synCsn (synC0c)))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) (synCsn (synC0c))
      p0013
  have p0015 :=
    @gEqtr3i (synCun (synCsn (synC0c)) (synCdif (synCnnc) (synCsn (synC0c))))
      (synCnnc)
      (synCun (synCsn (synC0c)) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      p0006 p0014
  have p0016 :=
    @gEqcomi (synCnnc)
      (synCun (synCsn (synC0c)) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      p0015
  have p0017 :=
    @gXpeq2i
      (synCun (synCsn (synC0c)) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCnnc) X p0016
  have p0018 :=
    @gXpundi X (synCsn (synC0c))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
  have p0019 :=
    @gEqtr3i
      (synCxp X (synCun (synCsn (synC0c))
          (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCxp X (synCnnc))
      (synCun (synCxp X (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      p0017 p0018
  have p0020 :=
    @gEqcomi (synCxp X (synCnnc))
      (synCun (synCxp X (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_sucnnf1o`. -/
@[expose]
noncomputable def gSucnnf1o (y : Var) (z : Var) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWf1o (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))) :=
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
  have dv_cache_0001 : z ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))).fv :=
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
  have dv_cache_0004 : z ∉ ((synCplc (.cv w) (synC1c))).fv :=
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
  have dv_cache_0006 : z ∉ ((synCplc (.cv t) (synC1c))).fv :=
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
  have dv_cache_0007 : t ∉ ((synCnnc)).fv :=
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
  have dv_cache_0009 : w ∉ ((synCnnc)).fv :=
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
  have dv_cache_0010 : w ∉ ((synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))).fv :=
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
  have dv_cache_0011 : t ∉ ((synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))).fv :=
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
  have dv_cache_0012 : y ∉ ((synCnnc)).fv :=
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
  have dv_cache_0013 : y ∉ ((synCplc (.cv z) (synC1c))).fv :=
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
  have dv_cache_0016 : z ∉ ((synWne (.cv y) (synC0c))).fv :=
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
  have p0000 := @gEqid (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))
  have p0001 := @gPeano2 (.cv z)
  have p0002 := @gPeano3 (.cv z)
  have p0003 :=
    @gJca (.classMem (.cv z) (synCnnc))
      (.classMem (synCplc (.cv z) (synC1c)) (synCnnc))
      (synWne (synCplc (.cv z) (synC1c)) (synC0c)) p0001 p0002
  have p0004 := @gNnnzdf y
  have p0005 :=
    @gEleq2i (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCdif (synCnnc) (synCsn (synC0c))) (synCplc (.cv z) (synC1c)) p0004
  have p0006 := @gEldifsn (synCplc (.cv z) (synC1c)) (synCnnc) (synC0c)
  have p0007 :=
    @gBitri
      (.classMem (synCplc (.cv z) (synC1c))
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (.classMem (synCplc (.cv z) (synC1c)) (synCdif (synCnnc) (synCsn (synC0c))))
      (synWa (.classMem (synCplc (.cv z) (synC1c)) (synCnnc))
        (synWne (synCplc (.cv z) (synC1c)) (synC0c)))
      p0005 p0006
  have p0008 :=
    @gSylibr (.classMem (.cv z) (synCnnc))
      (synWa (.classMem (synCplc (.cv z) (synC1c)) (synCnnc))
        (synWne (synCplc (.cv z) (synC1c)) (synC0c)))
      (.classMem (synCplc (.cv z) (synC1c))
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      p0003 p0007
  have p0009 :=
    @gFmpti z (synCnnc) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCplc (.cv z) (synC1c)) (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))
      dv_cache_0001 dv_cache_0002 p0000 p0008
  have p0010 := @gAddceq1 (.cv z) (.cv w) (synC1c)
  have p0012 := @gVex w
  have p0013 := @gN1cex
  have p0014 := @gAddcex (.cv w) (synC1c) p0012 p0013
  have p0015 :=
    @gFvmpt z (.cv w) (synCplc (.cv z) (synC1c)) (synCplc (.cv w) (synC1c))
      (synCnnc) (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) dv_cache_0003
      dv_cache_0004 dv_cache_0001 p0010 p0000 p0014
  have p0016 :=
    @gAdantr (.classMem (.cv w) (synCnnc))
      (.classEq (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
        (synCplc (.cv w) (synC1c)))
      (.classMem (.cv t) (synCnnc)) p0015
  have p0017 := @gAddceq1 (.cv z) (.cv t) (synC1c)
  have p0019 := @gVex t
  have p0021 := @gAddcex (.cv t) (synC1c) p0019 p0013
  have p0022 :=
    @gFvmpt z (.cv t) (synCplc (.cv z) (synC1c)) (synCplc (.cv t) (synC1c))
      (synCnnc) (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) dv_cache_0005
      dv_cache_0006 dv_cache_0001 p0017 p0000 p0021
  have p0023 :=
    @gAdantl (.classMem (.cv t) (synCnnc))
      (.classEq (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t))
        (synCplc (.cv t) (synC1c)))
      (.classMem (.cv w) (synCnnc)) p0022
  have p0024 :=
    @gEqeq12d (synWa (.classMem (.cv w) (synCnnc)) (.classMem (.cv t) (synCnnc)))
      (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
      (synCplc (.cv w) (synC1c))
      (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t))
      (synCplc (.cv t) (synC1c)) p0016 p0023
  have p0025 := @gSuc11nnc (.cv w) (.cv t)
  have p0026 :=
    @gBitrd (synWa (.classMem (.cv w) (synCnnc)) (.classMem (.cv t) (synCnnc)))
      (.classEq (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
        (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t)))
      (.classEq (synCplc (.cv w) (synC1c)) (synCplc (.cv t) (synC1c)))
      (.classEq (.cv w) (.cv t)) p0024 p0025
  have p0027 :=
    @gBiimpd (synWa (.classMem (.cv w) (synCnnc)) (.classMem (.cv t) (synCnnc)))
      (.classEq (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
        (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t)))
      (.classEq (.cv w) (.cv t)) p0026
  have p0028 :=
    @gRgen2
      (.imp (.classEq (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
          (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t)))
        (.classEq (.cv w) (.cv t)))
      w t (synCnnc) (synCnnc) dv_cache_0007 dv_cache_0008 p0027
  have p0029 :=
    @gPm32i
      (synWf (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synWral w (synCnnc) (synWral t (synCnnc) (.imp (.classEq
              (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
              (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t)))
            (.classEq (.cv w) (.cv t)))))
      p0009 p0028
  have p0030 :=
    @gDff13 w t (synCnnc) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) dv_cache_0009 dv_cache_0007
      dv_cache_0010 dv_cache_0011 dv_cache_0008
  have p0031_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
          (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))) (synWa
          (synWf (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
            (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))) (synWral w (synCnnc)
            (synWral t (synCnnc) (.imp (.classEq
                  (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
                  (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t)))
                (.classEq (.cv w) (.cv t))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synCmpt synCnnc synCint
          synCplc synWrex synC1c synCrab synC0c synCsn synC0 synCdif synCvv
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
    @gMpbir
      (synWf1 (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synWa (synWf (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
          (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))) (synWral w (synCnnc)
          (synWral t (synCnnc) (.imp (.classEq
                (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv w))
                (synCfv (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (.cv t)))
              (.classEq (.cv w) (.cv t))))))
      p0029 p0031_e01_recanon
  have p0033 :=
    @gRnmpt z y (synCnnc) (synCplc (.cv z) (synC1c))
      (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) dv_cache_0012 dv_cache_0013
      dv_cache_0014 p0000
  have p0034 :=
    @gOlc (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (.classEq (.cv y) (synC0c))
  have p0035 := @gNnc0suc z (.cv y) dv_cache_0015
  have p0036 :=
    @gSylibr (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (synWo (.classEq (.cv y) (synC0c))
        (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))))
      (.classMem (.cv y) (synCnnc)) p0034 p0035
  have p0037 :=
    @gSimpr (.classMem (.cv z) (synCnnc))
      (.classEq (.cv y) (synCplc (.cv z) (synC1c)))
  have p0039 :=
    @gAdantr (.classMem (.cv z) (synCnnc))
      (synWne (synCplc (.cv z) (synC1c)) (synC0c))
      (.classEq (.cv y) (synCplc (.cv z) (synC1c))) p0002
  have p0040 :=
    @gEqnetrd
      (synWa (.classMem (.cv z) (synCnnc)) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (.cv y) (synCplc (.cv z) (synC1c)) (synC0c) p0037 p0039
  have p0041 :=
    @gEx (.classMem (.cv z) (synCnnc)) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))
      (synWne (.cv y) (synC0c)) p0040
  have p0042 :=
    @gRexlimiv (.classEq (.cv y) (synCplc (.cv z) (synC1c)))
      (synWne (.cv y) (synC0c)) z (synCnnc) dv_cache_0016 p0041
  have p0043 := (Nominal.biimpRefl (synWne (.cv y) (synC0c)))
  have p0044 :=
    @gSylib (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (synWne (.cv y) (synC0c)) (.neg (.classEq (.cv y) (synC0c))) p0042 p0043
  have p0045 :=
    @gJca (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c))) p0036 p0044
  have p0046 :=
    @gSimpr (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c)))
  have p0047 :=
    @gPm221d (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c))))
      (.classEq (.cv y) (synC0c))
      (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))) p0046
  have p0048 :=
    @gId (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
  have p0049 :=
    @gA1i
      (.imp (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
        (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))))
      (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c)))) p0048
  have p0050 :=
    @gSimpl (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c)))
  have p0052 :=
    @gBiimpi (.classMem (.cv y) (synCnnc))
      (synWo (.classEq (.cv y) (synC0c))
        (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))))
      p0035
  have p0053 :=
    @gSyl (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c))))
      (.classMem (.cv y) (synCnnc))
      (synWo (.classEq (.cv y) (synC0c))
        (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))))
      p0050 p0052
  have p0054 :=
    @gMpjaod (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c))))
      (.classEq (.cv y) (synC0c))
      (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))) p0047 p0049
      p0053
  have p0055 :=
    @gImpbii (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c)))) p0045
      p0054
  have p0056 :=
    @gAbbii (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c))))
      (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c)))) y p0055
  have p0057 :=
    (Nominal.classEqRefl (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
  have p0058 :=
    @gEqtr4i
      (.cab y (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))))
      (.cab y (synWa (.classMem (.cv y) (synCnnc)) (.neg (.classEq (.cv y) (synC0c)))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) p0056 p0057
  have p0059 :=
    @gEqtri (synCrn (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
      (.cab y (synWrex z (synCnnc) (.classEq (.cv y) (synCplc (.cv z) (synC1c)))))
      (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) p0033 p0058
  have p0060 :=
    @gPm32i
      (synWf1 (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (.classEq (synCrn (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      p0031 p0059
  have p0061 :=
    @gDff1o5 (synCnnc) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))
  have p0062 :=
    @gMpbir
      (synWf1o (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synWa (synWf1 (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
          (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
        (.classEq (synCrn (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
          (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      p0060 p0061
  exact p0062

/-- Checked nominal proof certificate identified upstream as `g_padontoex`. -/
@[expose]
noncomputable def gPadontoex (x : Var) (y : Var) (v : Var) (f : Var) (F : Class)
    (dv_F_f : f ∉ F.fv) (_dv_F_v : v ∉ F.fv) (_dv_F_x : x ∉ F.fv) (_dv_F_y : y ∉ F.fv)
    (dv_f_v : f ≠ v) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) (_dv_v_x : v ≠ x) (_dv_v_y : v ≠ y)
    (_dv_x_y : x ≠ y) (hyp_padontoex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
            (synCres (synCid) (synCxp (.cv x)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
          (synCxp (.cv x) (synCnnc)) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synWex f (synWfo (.cv f) (synCxp (.cv x) (synCnnc))
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv x)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))) :=
  by
  have dv_cache_0001 :
    f ∉
      ((synCun (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCres (synCid)
            (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))).fv :=
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
      ((synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
            (synCres (synCid) (synCxp (.cv x)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
          (synCxp (.cv x) (synCnnc)) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))).fv :=
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
  have p0000 := @gIdex
  have p0001 := @gSnex (synC0c)
  have p0002 := @gResex (synCid) (synCsn (synC0c)) p0000 p0001
  have p0003 := @gPprodexg F (synCres (synCid) (synCsn (synC0c))) (synCvv) (synCvv)
  have p0004 :=
    @gMpan2 (.classMem F (synCvv))
      (.classMem (synCres (synCid) (synCsn (synC0c))) (synCvv))
      (.classMem (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCvv)) p0002
      p0003
  have p0006 := @gVex x
  have p0007 := @gNnnzex y
  have p0008 :=
    @gXpex (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))) p0006
      p0007
  have p0009 :=
    @gResex (synCid)
      (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))) p0000
      p0008
  have p0010 :=
    @gA1i
      (.classMem (synCres (synCid)
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCvv))
      (.classMem F (synCvv)) p0009
  have p0011 :=
    @gJca (.classMem F (synCvv))
      (.classMem (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCvv))
      (.classMem (synCres (synCid)
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCvv))
      p0004 p0010
  have p0012 :=
    @gUnexg (synCpprod F (synCres (synCid) (synCsn (synC0c))))
      (synCres (synCid)
        (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCvv) (synCvv)
  have p0013 :=
    @gSyl (.classMem F (synCvv))
      (synWa (.classMem (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCvv))
        (.classMem (synCres (synCid)
            (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
          (synCvv)))
      (.classMem (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid) (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))) (synCvv))
      p0011 p0012
  have p0014 :=
    @gFoeq1 (synCxp (.cv x) (synCnnc))
      (synCun (synCxp (.cv v) (synCsn (synC0c)))
        (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (.cv f)
      (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCres (synCid)
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
  have p0015 :=
    @gSpcegv
      (synWfo (.cv f) (synCxp (.cv x) (synCnnc))
        (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid) (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synCxp (.cv x) (synCnnc)) (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      f
      (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCres (synCid)
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (synCvv) dv_cache_0001 dv_cache_0002 p0014
  have p0016 :=
    @gSyl (.classMem F (synCvv))
      (.classMem (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid) (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))) (synCvv))
      (.imp (synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
            (synCres (synCid) (synCxp (.cv x)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
          (synCxp (.cv x) (synCnnc)) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synWex f (synWfo (.cv f) (synCxp (.cv x) (synCnnc))
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv x)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))))
      p0013 p0015
  have p0017 := Nominal.mp hyp_padontoex_1 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_sucxpinjex`. -/
@[expose]
noncomputable def gSucxpinjex (x : Var) (y : Var) (z : Var) (v : Var) (g : Var)
    (dv_g_v : g ≠ v) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_g_z : g ≠ z) (_dv_v_x : v ≠ x)
    (_dv_v_y : v ≠ y) (_dv_v_z : v ≠ z) (_dv_x_y : x ≠ y) (_dv_x_z : x ≠ z)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWf1 (synCpprod (synCres (synCid) (.cv x))
            (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))) (synCxp (.cv x) (synCnnc))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))) (synWex g
          (synWf1 (.cv g) (synCxp (.cv x) (synCnnc))
            (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv x)
                (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))) :=
  by
  have dv_cache_0001 : z ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((synCnnc)).fv :=
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
      ((synCpprod (synCres (synCid) (.cv x))
          (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))).fv :=
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
      ((synWf1 (synCpprod (synCres (synCid) (.cv x))
            (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))) (synCxp (.cv x) (synCnnc))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))).fv :=
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
  have p0000 := @gIdex
  have p0001 := @gVex x
  have p0002 := @gResex (synCid) (.cv x) p0000 p0001
  have p0003 := @gSsv (synCnnc)
  have p0004 :=
    @gResmpt z (synCvv) (synCnnc) (synCplc (.cv z) (synC1c)) dv_cache_0001
      dv_cache_0002
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gCsucex z
  have p0007 := @gNncex
  have p0008 :=
    @gResex (synCmpt z (synCvv) (synCplc (.cv z) (synC1c))) (synCnnc) p0006 p0007
  have p0009 :=
    @gEqeltrri (synCres (synCmpt z (synCvv) (synCplc (.cv z) (synC1c))) (synCnnc))
      (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCvv) p0005 p0008
  have p0010 :=
    @gPprodex (synCres (synCid) (.cv x))
      (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) p0002 p0009
  have p0011 :=
    @gF1eq1 (synCxp (.cv x) (synCnnc))
      (synCun (synCxp (.cv v) (synCsn (synC0c)))
        (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (.cv g)
      (synCpprod (synCres (synCid) (.cv x))
        (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
  have p0012 :=
    @gSpcev
      (synWf1 (.cv g) (synCxp (.cv x) (synCnnc))
        (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (synWf1 (synCpprod (synCres (synCid) (.cv x))
          (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))) (synCxp (.cv x) (synCnnc))
        (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      g
      (synCpprod (synCres (synCid) (.cv x))
        (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
      dv_cache_0003 dv_cache_0004 p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_sucxpinj`. -/
@[expose]
noncomputable def gSucxpinj (y : Var) (z : Var) (V : Class) (X : Class)
    (_dv_V_X : Disjoint V.fv X.fv) (_dv_V_y : y ∉ V.fv) (_dv_V_z : z ∉ V.fv)
    (_dv_X_y : y ∉ X.fv) (_dv_X_z : z ∉ X.fv) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWf1 (synCpprod (synCres (synCid) X)
          (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))) (synCxp X (synCnnc))
        (synCun (synCxp V (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))) :=
  by
  have dv_cache_0001 : y ≠ z := by exact (show y ≠ z from (by exact dv_y_z))
  have p0000 := @gF1oi X
  have p0001 := @gSucnnf1o y z dv_cache_0001
  have p0002 :=
    @gPm32i (synWf1o (synCres (synCid) X) X X)
      (synWf1o (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))) (synCnnc)
        (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      p0000 p0001
  have p0003 :=
    @gF1opprod X (synCnnc) X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))
      (synCres (synCid) X) (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gF1of1 (synCxp X (synCnnc))
      (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCpprod (synCres (synCid) X) (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gSsun2 (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCxp V (synCsn (synC0c)))
  have p0008 :=
    @gPm32i
      (synWf1 (synCpprod (synCres (synCid) X)
          (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c)))) (synCxp X (synCnnc))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synWss (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
        (synCun (synCxp V (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      p0006 p0007
  have p0009 :=
    @gF1ss (synCxp X (synCnnc))
      (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCun (synCxp V (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCpprod (synCres (synCid) X) (synCmpt z (synCnnc) (synCplc (.cv z) (synC1c))))
  have p0010 := Nominal.mp p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wpppadonto`. -/
@[expose]
noncomputable def gWpppadonto (y : Var) (F : Class) (V : Class) (X : Class)
    (_dv_F_V : Disjoint F.fv V.fv) (_dv_F_X : Disjoint F.fv X.fv) (_dv_F_y : y ∉ F.fv)
    (_dv_V_X : Disjoint V.fv X.fv) (_dv_V_y : y ∉ V.fv) (dv_X_y : y ∉ X.fv) :
    Nominal.NPrf
      (.imp (synWfo F X V) (synWfo
          (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCres (synCid)
              (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
          (synCxp X (synCnnc)) (synCun (synCxp V (synCsn (synC0c)))
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))) :=
  by
  have dv_cache_0001 : y ∉ (X).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_y, not_false_eq_true])
  have p0000 := @gId (synWfo F X V)
  have p0001 := @gF1oi (synCsn (synC0c))
  have p0002 :=
    @gF1ofo (synCsn (synC0c)) (synCsn (synC0c))
      (synCres (synCid) (synCsn (synC0c)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gJctir (synWfo F X V) (synWfo F X V)
      (synWfo (synCres (synCid) (synCsn (synC0c))) (synCsn (synC0c)) (synCsn (synC0c)))
      p0000 p0003
  have p0005 :=
    @gFopprod X (synCsn (synC0c)) V (synCsn (synC0c)) F
      (synCres (synCid) (synCsn (synC0c)))
  have p0006 :=
    @gSyl (synWfo F X V)
      (synWa (synWfo F X V)
        (synWfo (synCres (synCid) (synCsn (synC0c))) (synCsn (synC0c))
          (synCsn (synC0c))))
      (synWfo (synCpprod F (synCres (synCid) (synCsn (synC0c))))
        (synCxp X (synCsn (synC0c))) (synCxp V (synCsn (synC0c))))
      p0004 p0005
  have p0007 :=
    @gF1oi (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
  have p0008 :=
    @gF1ofo (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCres (synCid)
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gJctir (synWfo F X V)
      (synWfo (synCpprod F (synCres (synCid) (synCsn (synC0c))))
        (synCxp X (synCsn (synC0c))) (synCxp V (synCsn (synC0c))))
      (synWfo (synCres (synCid)
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      p0006 p0009
  have p0011 := @gXnndisj y X dv_cache_0001
  have p0012 :=
    @gJctir (synWfo F X V)
      (synWa (synWfo (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCxp X (synCsn (synC0c))) (synCxp V (synCsn (synC0c)))) (synWfo
          (synCres (synCid)
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (.classEq (synCin (synCxp X (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))) (synC0))
      p0010 p0011
  have p0013 :=
    @gFoun (synCxp X (synCsn (synC0c)))
      (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCxp V (synCsn (synC0c)))
      (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
      (synCpprod F (synCres (synCid) (synCsn (synC0c))))
      (synCres (synCid)
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
  have p0014 :=
    @gSyl (synWfo F X V)
      (synWa (synWa (synWfo (synCpprod F (synCres (synCid) (synCsn (synC0c))))
            (synCxp X (synCsn (synC0c))) (synCxp V (synCsn (synC0c)))) (synWfo
            (synCres (synCid)
              (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))) (.classEq
          (synCin (synCxp X (synCsn (synC0c)))
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))) (synC0)))
      (synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid)
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synCun (synCxp X (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCun (synCxp V (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      p0012 p0013
  have p0015 := @gXnnun y X dv_cache_0001
  have p0016 :=
    @gFoeq2
      (synCun (synCxp X (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCxp X (synCnnc))
      (synCun (synCxp V (synCsn (synC0c)))
        (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c)))) (synCres (synCid)
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gSylib (synWfo F X V)
      (synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid)
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synCun (synCxp X (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
        (synCun (synCxp V (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (synWfo (synCun (synCpprod F (synCres (synCid) (synCsn (synC0c))))
          (synCres (synCid)
            (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
        (synCxp X (synCnnc)) (synCun (synCxp V (synCsn (synC0c)))
          (synCxp X (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      p0014 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_f1exco`. -/
@[expose]
noncomputable def gF1exco (t : Var) (A : Class) (B : Class) (C : Class) (h : Var)
    (k : Var) (dv_A_h : h ∉ A.fv) (dv_A_k : k ∉ A.fv) (dv_A_t : t ∉ A.fv)
    (dv_B_h : h ∉ B.fv) (_dv_B_k : k ∉ B.fv) (dv_B_t : t ∉ B.fv) (dv_C_h : h ∉ C.fv)
    (dv_C_k : k ∉ C.fv) (dv_C_t : t ∉ C.fv) (dv_h_k : h ≠ k) (dv_h_t : h ≠ t)
    (dv_k_t : k ≠ t) :
    Nominal.NPrf
      (.imp (synWa (synWex h (synWf1 (.cv h) B C)) (synWex t (synWf1 (.cv t) A B)))
        (synWex k (synWf1 (.cv k) A C))) :=
  by
  have dv_cache_0001 : t ∉ ((synWf1 (.cv h) B C)).fv := by
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
  have dv_cache_0002 : h ∉ ((synWf1 (.cv t) A B)).fv :=
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
  have dv_cache_0003 : k ∉ ((synCcom (.cv h) (.cv t))).fv :=
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
  have dv_cache_0004 : k ∉ ((synWf1 (synCcom (.cv h) (.cv t)) A C)).fv :=
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
  have dv_cache_0005 : h ∉ ((synWex k (synWf1 (.cv k) A C))).fv :=
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
  have dv_cache_0006 : t ∉ ((synWex k (synWf1 (.cv k) A C))).fv :=
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
    @gEeanv (synWf1 (.cv h) B C) (synWf1 (.cv t) A B) h t dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gBiimpri
      (synWex h (synWex t (synWa (synWf1 (.cv h) B C) (synWf1 (.cv t) A B))))
      (synWa (synWex h (synWf1 (.cv h) B C)) (synWex t (synWf1 (.cv t) A B))) p0000
  have p0002 := @gF1co A B C (.cv h) (.cv t)
  have p0003 := @gVex h
  have p0004 := @gVex t
  have p0005 := @gCoex (.cv h) (.cv t) p0003 p0004
  have p0006 := @gF1eq1 A C (.cv k) (synCcom (.cv h) (.cv t))
  have p0007 :=
    @gSpcev (synWf1 (.cv k) A C) (synWf1 (synCcom (.cv h) (.cv t)) A C) k
      (synCcom (.cv h) (.cv t)) dv_cache_0003 dv_cache_0004 p0005 p0006
  have p0008 :=
    @gSyl (synWa (synWf1 (.cv h) B C) (synWf1 (.cv t) A B))
      (synWf1 (synCcom (.cv h) (.cv t)) A C) (synWex k (synWf1 (.cv k) A C)) p0002
      p0007
  have p0009 :=
    @gExlimivv (synWa (synWf1 (.cv h) B C) (synWf1 (.cv t) A B))
      (synWex k (synWf1 (.cv k) A C)) h t dv_cache_0005 dv_cache_0006 p0008
  have p0010 :=
    @gSyl (synWa (synWex h (synWf1 (.cv h) B C)) (synWex t (synWf1 (.cv t) A B)))
      (synWex h (synWex t (synWa (synWf1 (.cv h) B C) (synWf1 (.cv t) A B))))
      (synWex k (synWf1 (.cv k) A C)) p0001 p0009
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

/-- Checked nominal proof certificate identified upstream as `g_taginjex`. -/
@[expose]
noncomputable def gTaginjex (x : Var) (y : Var) (v : Var) (t : Var) (dv_t_v : t ≠ v)
    (_dv_t_x : t ≠ x) (_dv_t_y : t ≠ y) (_dv_v_x : v ≠ x) (_dv_v_y : v ≠ y)
    (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWex t (synWf1 (.cv t) (.cv v) (synCun (synCxp (.cv v) (synCsn (synC0c)))
            (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))) :=
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
  have dv_cache_0002 : t ∉ ((synCxp (.cv v) (synCsn (synC0c)))).fv :=
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
  have p0000 := @gVex v
  have p0001 := @gN0cex
  have p0002 := @gXpsnen (.cv v) (synC0c) p0000 p0001
  have p0003 := @gEnsym (synCxp (.cv v) (synCsn (synC0c))) (.cv v)
  have p0004 :=
    @gMpbi (synWbr (synCxp (.cv v) (synCsn (synC0c))) (synCen) (.cv v))
      (synWbr (.cv v) (synCen) (synCxp (.cv v) (synCsn (synC0c)))) p0002 p0003
  have p0005 :=
    @gBren (.cv v) (synCxp (.cv v) (synCsn (synC0c))) t dv_cache_0001 dv_cache_0002
  have p0006 :=
    @gMpbi (synWbr (.cv v) (synCen) (synCxp (.cv v) (synCsn (synC0c))))
      (synWex t (synWf1o (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c))))) p0004
      p0005
  have p0007 := @gF1of1 (.cv v) (synCxp (.cv v) (synCsn (synC0c))) (.cv t)
  have p0008 :=
    @gSsun1 (synCxp (.cv v) (synCsn (synC0c)))
      (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))
  have p0009 :=
    @gA1i
      (synWss (synCxp (.cv v) (synCsn (synC0c)))
        (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      (synWf1o (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c)))) p0008
  have p0010 :=
    @gJca (synWf1o (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c))))
      (synWf1 (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c))))
      (synWss (synCxp (.cv v) (synCsn (synC0c)))
        (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      p0007 p0009
  have p0011 :=
    @gF1ss (.cv v) (synCxp (.cv v) (synCsn (synC0c)))
      (synCun (synCxp (.cv v) (synCsn (synC0c)))
        (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))
      (.cv t)
  have p0012 :=
    @gSyl (synWf1o (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c))))
      (synWa (synWf1 (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c))))
        (synWss (synCxp (.cv v) (synCsn (synC0c)))
          (synCun (synCxp (.cv v) (synCsn (synC0c))) (synCxp (.cv x)
              (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c))))))))
      (synWf1 (.cv t) (.cv v) (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      p0010 p0011
  have p0013 :=
    @gEximi (synWf1o (.cv t) (.cv v) (synCxp (.cv v) (synCsn (synC0c))))
      (synWf1 (.cv t) (.cv v) (synCun (synCxp (.cv v) (synCsn (synC0c)))
          (synCxp (.cv x) (synCrab y (synCnnc) (.neg (.classEq (.cv y) (synC0c)))))))
      t p0012
  have p0014 := Nominal.mp p0006 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_qkrelbr`. -/
@[expose]
noncomputable def gQkrelbr (A : Class) (B : Class) (C : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (hyp_qkrelbr_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_qkrelbr_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk B C) (synCqkrel A)) (.classMem (synCop B C) A)) :=
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
  have dv_cache_0007 : x ∉ ((synCqkrel A)).fv :=
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
  have dv_cache_0008 : y ∉ ((synCqkrel A)).fv :=
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
  have dv_cache_0015 : y ∉ ((Wff.classMem (synCop B C) A)).fv :=
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
  have dv_cache_0016 : z ∉ ((Wff.classMem (synCop (.cv x) (.cv y)) A)).fv :=
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
  have dv_cache_0017 : x ∉ ((Wff.classMem (synCop B (.cv y)) A)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQkrel x y z A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := @gOpeq1 (.cv x) B (.cv y)
  have p0002 :=
    @gEleq1d (.classEq (.cv x) B) (synCop (.cv x) (.cv y)) (synCop B (.cv y)) A p0001
  have p0003 := @gOpeq2 (.cv y) C B
  have p0004 := @gEleq1d (.classEq (.cv y) C) (synCop B (.cv y)) (synCop B C) A p0003
  have p0005 :=
    @gOpkelopkab (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop B (.cv y)) A) (.classMem (synCop B C) A) z x y (synCqkrel A) B
      C dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0004 p0000 p0002 p0004 hyp_qkrelbr_1
      hyp_qkrelbr_2
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fdmemval`. -/
@[expose]
noncomputable def gFdmemval (C : Class) (e : Var) (_dv_C_e : e ∉ C.fv)
    (hyp_fdmemval_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
        (.classMem C (.cv e))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdmem))
  have p0001 :=
    @gEleq2i (synCfdmem) (synCcnvk (synCsik (synCssetk)))
      (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) p0000
  have p0002 := @gSnex (.cv e)
  have p0003 := @gSnex (synCsn C)
  have p0004 :=
    @gOpkelcnvk (synCsn (.cv e)) (synCsn (synCsn C)) (synCsik (synCssetk)) p0002
      p0003
  have p0005 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C)))
        (synCcnvk (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn C)) (synCsn (.cv e))) (synCsik (synCssetk)))
      p0001 p0004
  have p0006 := @gSnex C
  have p0007 := @gVex e
  have p0008 := @gOpksnelsik (synCsn C) (.cv e) (synCssetk) p0006 p0007
  have p0009 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem (synCopk (synCsn (synCsn C)) (synCsn (.cv e))) (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn C) (.cv e)) (synCssetk)) p0005 p0008
  have p0011 := @gElssetk C (.cv e) hyp_fdmemval_1 p0007
  have p0012 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem (synCopk (synCsn C) (.cv e)) (synCssetk)) (.classMem C (.cv e)) p0009
      p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_qkrelex`. -/
@[expose]
noncomputable def gQkrelex (A : Class)
    (hyp_qkrelex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCqkrel A) (synCvv)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQkrel x y z A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gSetconslem6 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0002 :=
    @gEqtr4i (synCqkrel A)
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.classMem (synCop (.cv x) (.cv y)) A)))))
      (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
            (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                  (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 A)))
      p0000 p0001
  have p0003 := @gVvex
  have p0006 := @gXpkex (synCvv) (synCvv) p0003 p0003
  have p0007 := @gXpkex (synCvv) (synCxpk (synCvv) (synCvv)) p0003 p0006
  have p0008 := @gSetconslem5
  have p0009 :=
    @gInex (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
      (synCcompl (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
            (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                  (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0007 p0008
  have p0010 := @gPw1ex A hyp_qkrelex_1
  have p0011 := @gPw1ex (synCpw1 A) p0010
  have p0012 :=
    @gImakex
      (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCpw1 (synCpw1 A)) p0009 p0011
  have p0013 :=
    @gEqeltri (synCqkrel A)
      (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
            (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                  (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 A)))
      (synCvv) p0002 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_fdmemex`. -/
@[expose]
noncomputable def gFdmemex : Nominal.NPrf (.classMem (synCfdmem) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdmem))
  have p0001 := @gSsetkex
  have p0002 := @gSikex (synCssetk) p0001
  have p0003 := @gCnvkex (synCsik (synCssetk)) p0002
  have p0004 :=
    @gEqeltri (synCfdmem) (synCcnvk (synCsik (synCssetk))) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fdprj0ex`. -/
@[expose]
noncomputable def gFdprj0ex : Nominal.NPrf (.classMem (synCfdprj0) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdprj0))
  have p0001 := @gIdkex
  have p0002 := @gIns3kex (synCidk) p0001
  have p0003 := @gEqeltri (synCfdprj0) (synCins3k (synCidk)) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fdprj1ex`. -/
@[expose]
noncomputable def gFdprj1ex : Nominal.NPrf (.classMem (synCfdprj1) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdprj1))
  have p0001 := @gIdkex
  have p0002 := @gIns2kex (synCidk) p0001
  have p0003 := @gEqeltri (synCfdprj1) (synCins2k (synCidk)) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fddomex`. -/
@[expose]
noncomputable def gFddomex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfddom A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfddom A B))
  have p0001 := @gPw1ex A hyp_fddomex_1
  have p0002 := @gXpkex B B hyp_fddomex_2 hyp_fddomex_2
  have p0003 := @gXpkex (synCpw1 A) (synCxpk B B) p0001 p0002
  have p0004 :=
    @gEqeltri (synCfddom A B) (synCxpk (synCpw1 A) (synCxpk B B)) (synCvv) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fde0ex`. -/
@[expose]
noncomputable def gFde0ex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfde0 A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfde0 A B))
  have p0001 := @gFdprj0ex
  have p0002 := @gFdmemex
  have p0003 := @gCokex (synCfdprj0) (synCfdmem) p0001 p0002
  have p0004 := @gFddomex A B hyp_fddomex_1 hyp_fddomex_2
  have p0005 :=
    @gInex (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B) p0003 p0004
  have p0006 :=
    @gEqeltri (synCfde0 A B)
      (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B)) (synCvv) p0000
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fde1ex`. -/
@[expose]
noncomputable def gFde1ex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfde1 A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfde1 A B))
  have p0001 := @gFdprj1ex
  have p0002 := @gFdmemex
  have p0003 := @gCokex (synCfdprj1) (synCfdmem) p0001 p0002
  have p0004 := @gFddomex A B hyp_fddomex_1 hyp_fddomex_2
  have p0005 :=
    @gInex (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B) p0003 p0004
  have p0006 :=
    @gEqeltri (synCfde1 A B)
      (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B)) (synCvv) p0000
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fdsepex`. -/
@[expose]
noncomputable def gFdsepex (A : Class) (B : Class)
    (hyp_fddomex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fddomex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdsep A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdsep A B))
  have p0001 := @gFde0ex A B hyp_fddomex_1 hyp_fddomex_2
  have p0002 := @gFde1ex A B hyp_fddomex_1 hyp_fddomex_2
  have p0003 := @gSymdifex (synCfde0 A B) (synCfde1 A B) p0001 p0002
  have p0004 :=
    @gEqeltri (synCfdsep A B) (synCsymdif (synCfde0 A B) (synCfde1 A B)) (synCvv)
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fdliftex`. -/
@[expose]
noncomputable def gFdliftex (R : Class)
    (hyp_fdliftex_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classMem (synCfdlift R) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdlift R))
  have p0001 := @gQkrelex R hyp_fdliftex_1
  have p0002 := @gSikex (synCqkrel R) p0001
  have p0003 := @gEqeltri (synCfdlift R) (synCsik (synCqkrel R)) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fdnonminex`. -/
@[expose]
noncomputable def gFdnonminex (A : Class) (B : Class) (R : Class)
    (hyp_fdnonminex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdnonminex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdnonminex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdnonmin R A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdnonmin R A B))
  have p0001 := @gFdsepex A B hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0002 := @gIdex
  have p0003 := @gDifex R (synCid) hyp_fdnonminex_1 p0002
  have p0004 := @gFdliftex (synCdif R (synCid)) p0003
  have p0005 := @gCnvkex (synCfdlift (synCdif R (synCid))) p0004
  have p0006 :=
    @gCokex (synCfdsep A B) (synCcnvk (synCfdlift (synCdif R (synCid)))) p0001 p0005
  have p0007 :=
    @gEqeltri (synCfdnonmin R A B)
      (synCcomk (synCfdsep A B) (synCcnvk (synCfdlift (synCdif R (synCid)))))
      (synCvv) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_fdminsepex`. -/
@[expose]
noncomputable def gFdminsepex (A : Class) (B : Class) (R : Class)
    (hyp_fdnonminex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdnonminex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdnonminex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdminsep R A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdminsep R A B))
  have p0001 := @gFdsepex A B hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0002 := @gFdnonminex A B R hyp_fdnonminex_1 hyp_fdnonminex_2 hyp_fdnonminex_3
  have p0003 := @gDifex (synCfdsep A B) (synCfdnonmin R A B) p0001 p0002
  have p0004 :=
    @gEqeltri (synCfdminsep R A B) (synCdif (synCfdsep A B) (synCfdnonmin R A B))
      (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fdliftval2`. -/
@[expose]
noncomputable def gFdliftval2 (x : Var) (R : Class) (e : Var) (c : Var) (d : Var)
    (dv_R_c : c ∉ R.fv) (dv_R_d : d ∉ R.fv) (_dv_R_e : e ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_c_d : c ≠ d) (dv_c_e : c ≠ e) (dv_c_x : c ≠ x) (dv_d_e : d ≠ e) (dv_d_x : d ≠ x)
    (_dv_e_x : e ≠ x) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCfdlift R)) (synWex c
          (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
              (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))))) :=
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
  have dv_cache_0003 : c ∉ ((synCsn (.cv e))).fv :=
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
  have dv_cache_0004 : d ∉ ((synCsn (.cv e))).fv :=
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
  have dv_cache_0005 : c ∉ ((synCqkrel R)).fv :=
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
  have dv_cache_0006 : d ∉ ((synCqkrel R)).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCfdlift R))
  have p0001 :=
    @gEleq2i (synCfdlift R) (synCsik (synCqkrel R))
      (synCopk (.cv x) (synCsn (.cv e))) p0000
  have p0002 := @gVex x
  have p0003 := @gSnex (.cv e)
  have p0004 :=
    @gPm32i (.classMem (.cv x) (synCvv)) (.classMem (synCsn (.cv e)) (synCvv)) p0002
      p0003
  have p0005 :=
    @gOpkelsikg c d (.cv x) (synCsn (.cv e)) (synCqkrel R) (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gVex c
  have p0008 := @gVex d
  have p0009 :=
    @gQkrelbr R (.cv c) (.cv d) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0007 p0008
  have p0010 := (Nominal.biimpRefl (synWbr (.cv c) R (.cv d)))
  have p0011 :=
    @gBicomi (synWbr (.cv c) R (.cv d)) (.classMem (synCop (.cv c) (.cv d)) R) p0010
  have p0012 :=
    @gBitri (.classMem (synCopk (.cv c) (.cv d)) (synCqkrel R))
      (.classMem (synCop (.cv c) (.cv d)) R) (synWbr (.cv c) R (.cv d)) p0009 p0011
  have p0013 :=
    @gN3anbi3i (.classMem (synCopk (.cv c) (.cv d)) (synCqkrel R))
      (synWbr (.cv c) R (.cv d)) (.classEq (.cv x) (synCsn (.cv c)))
      (.classEq (synCsn (.cv e)) (synCsn (.cv d))) p0012
  have p0014 :=
    @gExbii
      (synW3a (.classEq (.cv x) (synCsn (.cv c)))
        (.classEq (synCsn (.cv e)) (synCsn (.cv d)))
        (.classMem (synCopk (.cv c) (.cv d)) (synCqkrel R)))
      (synW3a (.classEq (.cv x) (synCsn (.cv c)))
        (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))
      d p0013
  have p0015 :=
    @gExbii
      (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
          (.classEq (synCsn (.cv e)) (synCsn (.cv d)))
          (.classMem (synCopk (.cv c) (.cv d)) (synCqkrel R))))
      (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
          (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d))))
      c p0014
  have p0016 :=
    @gBitri (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCsik (synCqkrel R)))
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (synCsn (.cv e)) (synCsn (.cv d)))
            (.classMem (synCopk (.cv c) (.cv d)) (synCqkrel R)))))
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))))
      p0006 p0015
  have p0017 :=
    @gBitri (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCfdlift R))
      (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCsik (synCqkrel R)))
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))))
      p0001 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_fdliftval1`. -/
@[expose]
noncomputable def gFdliftval1 (x : Var) (R : Class) (e : Var) (c : Var)
    (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_c_e : c ≠ e)
    (dv_c_x : c ≠ x) (dv_e_x : e ≠ x) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCfdlift R)) (synWex c
          (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e))))) :=
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
    d ∉ ((synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e)))).fv :=
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
    @gFdliftval2 x R e c d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @gVex e
  have p0002 := @gSneqb (.cv e) (.cv d) p0001
  have p0003 := @gEqcom (.cv e) (.cv d)
  have p0004 :=
    @gBitri (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (.classEq (.cv e) (.cv d))
      (.classEq (.cv d) (.cv e)) p0002 p0003
  have p0005 :=
    @gN3anbi2i (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (.classEq (.cv d) (.cv e))
      (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv d)) p0004
  have p0006 :=
    @gN3ancoma (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv d) (.cv e))
      (synWbr (.cv c) R (.cv d))
  have p0007 :=
    @gBitri
      (synW3a (.classEq (.cv x) (synCsn (.cv c)))
        (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))
      (synW3a (.classEq (.cv x) (synCsn (.cv c))) (.classEq (.cv d) (.cv e))
        (synWbr (.cv c) R (.cv d)))
      (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
        (synWbr (.cv c) R (.cv d)))
      p0005 p0006
  have p0008 :=
    @gExbii
      (synW3a (.classEq (.cv x) (synCsn (.cv c)))
        (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))
      (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
        (synWbr (.cv c) R (.cv d)))
      d p0007
  have p0009 :=
    @gExbii
      (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
          (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d))))
      (synWex d (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
          (synWbr (.cv c) R (.cv d))))
      c p0008
  have p0010 :=
    @gN3anass (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
      (synWbr (.cv c) R (.cv d))
  have p0011 :=
    @gExbii
      (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
        (synWbr (.cv c) R (.cv d)))
      (synWa (.classEq (.cv d) (.cv e))
        (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv d))))
      d p0010
  have p0013 := @gBreq2 (.cv d) (.cv e) (.cv c) R
  have p0014 :=
    @gAnbi2d (.classEq (.cv d) (.cv e)) (synWbr (.cv c) R (.cv d))
      (synWbr (.cv c) R (.cv e)) (.classEq (.cv x) (synCsn (.cv c))) p0013
  have p0015 :=
    @gCeqsexv (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv d)))
      (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e))) d (.cv e)
      dv_cache_0011 dv_cache_0012 p0001 p0014
  have p0016 :=
    @gBitri
      (synWex d (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
          (synWbr (.cv c) R (.cv d))))
      (synWex d (synWa (.classEq (.cv d) (.cv e))
          (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv d)))))
      (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e))) p0011
      p0015
  have p0017 :=
    @gExbii
      (synWex d (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
          (synWbr (.cv c) R (.cv d))))
      (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e))) c p0016
  have p0018 :=
    @gBitri
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))))
      (synWex c (synWex d
          (synW3a (.classEq (.cv d) (.cv e)) (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) R (.cv d)))))
      (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e))))
      p0009 p0017
  have p0019 :=
    @gBitri (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCfdlift R))
      (synWex c (synWex d (synW3a (.classEq (.cv x) (synCsn (.cv c)))
            (.classEq (synCsn (.cv e)) (synCsn (.cv d))) (synWbr (.cv c) R (.cv d)))))
      (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c))) (synWbr (.cv c) R (.cv e))))
      p0000 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_fdmemvalC`. -/
@[expose]
noncomputable def gFdmemvalC (B : Class) (C : Class) (e : Var) :
    Nominal.NPrf
      (.imp (.classMem C B) (synWb
          (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
          (.classMem C (.cv e)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdmem))
  have p0001 :=
    @gEleq2i (synCfdmem) (synCcnvk (synCsik (synCssetk)))
      (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) p0000
  have p0002 := @gSnex (.cv e)
  have p0003 := @gSnex (synCsn C)
  have p0004 :=
    @gOpkelcnvk (synCsn (.cv e)) (synCsn (synCsn C)) (synCsik (synCssetk)) p0002
      p0003
  have p0005 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C)))
        (synCcnvk (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn C)) (synCsn (.cv e))) (synCsik (synCssetk)))
      p0001 p0004
  have p0006 := @gSnex C
  have p0007 := @gVex e
  have p0008 := @gOpksnelsik (synCsn C) (.cv e) (synCssetk) p0006 p0007
  have p0009 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem (synCopk (synCsn (synCsn C)) (synCsn (.cv e))) (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn C) (.cv e)) (synCssetk)) p0005 p0008
  have p0010 := @gElex C B
  have p0012 := @gA1i (.classMem (.cv e) (synCvv)) (.classMem C B) p0007
  have p0013 :=
    @gJca (.classMem C B) (.classMem C (synCvv)) (.classMem (.cv e) (synCvv)) p0010
      p0012
  have p0014 := @gElssetkg C (.cv e) (synCvv) (synCvv)
  have p0015 :=
    @gSyl (.classMem C B) (synWa (.classMem C (synCvv)) (.classMem (.cv e) (synCvv)))
      (synWb (.classMem (synCopk (synCsn C) (.cv e)) (synCssetk)) (.classMem C (.cv e)))
      p0013 p0014
  have p0016 :=
    @gSyl5bb (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem (synCopk (synCsn C) (.cv e)) (synCssetk)) (.classMem C B)
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

/-- Checked nominal proof certificate identified upstream as `g_fdprj0valV`. -/
@[expose]
noncomputable def gFdprj0valV (x : Var) (C : Class) (D : Class)
    (_dv_C_D : Disjoint C.fv D.fv) (_dv_C_x : x ∉ C.fv) (_dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
        (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
          (.classEq (.cv x) (synCsn (synCsn C))))) :=
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
  have dv_cache_0004 : a ∉ ((synCopk C D)).fv :=
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
  have dv_cache_0005 : b ∉ ((synCopk C D)).fv :=
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
  have dv_cache_0006 : c ∉ ((synCopk C D)).fv :=
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
  have dv_cache_0007 : a ∉ ((synCidk)).fv :=
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
  have dv_cache_0008 : b ∉ ((synCidk)).fv :=
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
  have dv_cache_0009 : c ∉ ((synCidk)).fv :=
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
    a ∉ ((synWa (.classMem C (synCvv)) (.classMem D (synCvv)))).fv :=
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
    b ∉ ((synWa (.classMem C (synCvv)) (.classMem D (synCvv)))).fv :=
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
    c ∉ ((synWa (.classMem C (synCvv)) (.classMem D (synCvv)))).fv :=
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
      ((synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))).fv :=
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
      ((synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C))).fv :=
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
  have dv_cache_0021 : a ∉ ((Wff.classEq (.cv x) (synCsn (synCsn C)))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCfdprj0))
  have p0001 :=
    @gEleq2i (synCfdprj0) (synCins3k (synCidk)) (synCopk (.cv x) (synCopk C D))
      p0000
  have p0002 := @gVex x
  have p0003 := @gOpkex C D
  have p0004 :=
    @gOpkelins3kg a b c (.cv x) (synCopk C D) (synCidk) (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0005 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem (synCopk C D) (synCvv))
      (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCins3k (synCidk))) (synWex a
          (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
                (.classMem (synCopk (.cv a) (.cv b)) (synCidk)))))))
      p0002 p0003 p0004
  have p0006 :=
    @gBitri (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCins3k (synCidk)))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
              (.classMem (synCopk (.cv a) (.cv b)) (synCidk))))))
      p0001 p0005
  have p0007 :=
    @gA1i
      (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0)) (synWex a (synWex b
            (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
                (.classMem (synCopk (.cv a) (.cv b)) (synCidk)))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0006
  have p0008 := @gBiid (.classEq (.cv x) (synCsn (synCsn (.cv a))))
  have p0009 :=
    @gA1i
      (synWb (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (.classEq (.cv x) (synCsn (synCsn (.cv a)))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0008
  have p0010 := @gVex c
  have p0011 := @gOpkthg C D (.cv b) (.cv c) (synCvv) (synCvv) (synCvv)
  have p0012 :=
    @gMp3an3 (.classMem C (synCvv)) (.classMem D (synCvv))
      (.classMem (.cv c) (synCvv))
      (synWb (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
        (synWa (.classEq C (.cv b)) (.classEq D (.cv c))))
      p0010 p0011
  have p0013 := @gEqcom C (.cv b)
  have p0014 := @gEqcom D (.cv c)
  have p0015 :=
    @gAnbi12i (.classEq C (.cv b)) (.classEq (.cv b) C) (.classEq D (.cv c))
      (.classEq (.cv c) D) p0013 p0014
  have p0016 :=
    @gA1i
      (synWb (synWa (.classEq C (.cv b)) (.classEq D (.cv c)))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0015
  have p0017 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
      (synWa (.classEq C (.cv b)) (.classEq D (.cv c)))
      (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) p0012 p0016
  have p0018 := @gVex a
  have p0019 := @gVex b
  have p0020 := @gOpkelidkg (.cv a) (.cv b) (synCvv) (synCvv)
  have p0021 :=
    @gMp2an (.classMem (.cv a) (synCvv)) (.classMem (.cv b) (synCvv))
      (synWb (.classMem (synCopk (.cv a) (.cv b)) (synCidk)) (.classEq (.cv a) (.cv b)))
      p0018 p0019 p0020
  have p0022 :=
    @gA1i
      (synWb (.classMem (synCopk (.cv a) (.cv b)) (synCidk)) (.classEq (.cv a) (.cv b)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0021
  have p0023 :=
    @gN3anbi123d (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
      (synWa (.classEq (.cv b) C) (.classEq (.cv c) D))
      (.classMem (synCopk (.cv a) (.cv b)) (synCidk)) (.classEq (.cv a) (.cv b)) p0009
      p0017 p0022
  have p0024 :=
    @gN3exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
        (.classMem (synCopk (.cv a) (.cv b)) (synCidk)))
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0023
  have p0025 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
              (.classMem (synCopk (.cv a) (.cv b)) (synCidk))))))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))))))
      p0007 p0024
  have p0026 :=
    @gN3anass (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))
  have p0027 :=
    @gAnass (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))
  have p0028 :=
    @gAnbi2i
      (synWa (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))))
      (.classEq (.cv x) (synCsn (synCsn (.cv a)))) p0027
  have p0029 :=
    @gBitri
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b)))))
      p0026 p0028
  have p0030 :=
    @gAn12 (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))
  have p0031 :=
    @gAnbi2i
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b))))
      (synWa (.classEq (.cv c) D) (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      (.classEq (.cv x) (synCsn (synCsn (.cv a)))) p0030
  have p0032 :=
    @gBitri
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv b)))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (synWa (.classEq (.cv c) D)
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      p0029 p0031
  have p0033 :=
    @gAn12 (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv c) D)
      (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))
  have p0034 :=
    @gBitri
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (synWa (.classEq (.cv c) D)
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      (synWa (.classEq (.cv c) D) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      p0032 p0033
  have p0035 :=
    @gA1i
      (synWb (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
        (synWa (.classEq (.cv c) D) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0034
  have p0036 :=
    @gN3exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b)))
      (synWa (.classEq (.cv c) D) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0035
  have p0037 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv b))))))
      (synWex a (synWex b (synWex c (synWa (.classEq (.cv c) D)
              (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))))
      p0025 p0036
  have p0038 := @gSimpr (.classMem C (synCvv)) (.classMem D (synCvv))
  have p0039 :=
    @gBiidd (.classEq (.cv c) D)
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
  have p0040 :=
    @gCeqsexgv
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      c D (synCvv) dv_cache_0016 dv_cache_0017 p0039
  have p0041 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem D (synCvv))
      (synWb (synWex c (synWa (.classEq (.cv c) D)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
        (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))))
      p0038 p0040
  have p0042 :=
    @gN2exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWex c (synWa (.classEq (.cv c) D)
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      a b dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWex b (synWex c (synWa (.classEq (.cv c) D)
              (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))))
      (synWex a (synWex b (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      p0037 p0042
  have p0044 :=
    @gAn12 (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv b) C)
      (.classEq (.cv a) (.cv b))
  have p0045 :=
    @gA1i
      (synWb (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)))) (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv b)))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0044
  have p0046 :=
    @gN2exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (.classEq (.cv a) (.cv b))))
      a b dv_cache_0013 dv_cache_0014 p0045
  have p0047 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWex b (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv b) C) (.classEq (.cv a) (.cv b))))))
      (synWex a (synWex b (synWa (.classEq (.cv b) C)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (.cv a) (.cv b))))))
      p0043 p0046
  have p0048 := @gSimpl (.classMem C (synCvv)) (.classMem D (synCvv))
  have p0049 := @gEqeq2 (.cv b) C (.cv a)
  have p0050 :=
    @gAnbi2d (.classEq (.cv b) C) (.classEq (.cv a) (.cv b)) (.classEq (.cv a) C)
      (.classEq (.cv x) (synCsn (synCsn (.cv a)))) p0049
  have p0051 :=
    @gCeqsexgv
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv b)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)) b C
      (synCvv) dv_cache_0018 dv_cache_0019 p0050
  have p0052 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem C (synCvv))
      (synWb (synWex b (synWa (.classEq (.cv b) C)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv b)))))
        (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)))
      p0048 p0051
  have p0053 :=
    @gExbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWex b (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv b)))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)) a
      dv_cache_0013 p0052
  have p0054 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWex b (synWa (.classEq (.cv b) C)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (.cv a) (.cv b))))))
      (synWex a (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)))
      p0047 p0053
  have p0055 :=
    @gAncom (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)
  have p0056 :=
    @gExbii (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C))
      (synWa (.classEq (.cv a) C) (.classEq (.cv x) (synCsn (synCsn (.cv a))))) a p0055
  have p0057 :=
    @gA1i
      (synWb (synWex a
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)))
        (synWex a
          (synWa (.classEq (.cv a) C) (.classEq (.cv x) (synCsn (synCsn (.cv a)))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0056
  have p0058 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) C)))
      (synWex a (synWa (.classEq (.cv a) C) (.classEq (.cv x) (synCsn (synCsn (.cv a))))))
      p0054 p0057
  have p0060 := @gSneq (.cv a) C
  have p0061 := @gSneqd (.classEq (.cv a) C) (synCsn (.cv a)) (synCsn C) p0060
  have p0062 :=
    @gEqeq2d (.classEq (.cv a) C) (synCsn (synCsn (.cv a))) (synCsn (synCsn C))
      (.cv x) p0061
  have p0063 :=
    @gCeqsexgv (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (.classEq (.cv x) (synCsn (synCsn C))) a C (synCvv) dv_cache_0020 dv_cache_0021
      p0062
  have p0064 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem C (synCvv))
      (synWb (synWex a
          (synWa (.classEq (.cv a) C) (.classEq (.cv x) (synCsn (synCsn (.cv a))))))
        (.classEq (.cv x) (synCsn (synCsn C))))
      p0048 p0063
  have p0065 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (synWex a (synWa (.classEq (.cv a) C) (.classEq (.cv x) (synCsn (synCsn (.cv a))))))
      (.classEq (.cv x) (synCsn (synCsn C))) p0058 p0064
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_fde0valJp`. -/
@[expose]
noncomputable def gFde0valJp (A : Class) (B : Class) (C : Class) (D : Class) (e : Var)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (_dv_A_e : e ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_D : Disjoint B.fv D.fv) (_dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (_dv_C_e : e ∉ C.fv) (_dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem C B) (.classMem D B))
        (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
          (synWa (.classMem (.cv e) A) (.classMem C (.cv e))))) :=
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
  have dv_cache_0001 : x ∉ ((synCsn (.cv e))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_e,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCopk C D)).fv :=
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
  have dv_cache_0003 : x ∉ ((synCfdprj0)).fv :=
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
  have dv_cache_0004 : x ∉ ((synCfdmem)).fv :=
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
  have dv_cache_0008 : x ∉ ((synWa (.classMem C B) (.classMem D B))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCsn (synCsn C))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCfde0 A B))
  have p0001 :=
    @gEleq2i (synCfde0 A B)
      (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B))))
      (synWa (.classMem C B) (.classMem D B)) p0001
  have p0003 :=
    @gElin (synCopk (synCsn (.cv e)) (synCopk C D))
      (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B)
  have p0004 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B))) (synWa
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
            (synCcomk (synCfdprj0) (synCfdmem)))
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))))
      (synWa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B)))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCcomk (synCfdprj0) (synCfdmem)))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B)))
      p0002 p0004
  have p0006 := @gSnex (.cv e)
  have p0007 := @gOpkex C D
  have p0008 :=
    @gOpkelcok x (synCsn (.cv e)) (synCopk C D) (synCfdprj0) (synCfdmem)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCcomk (synCfdprj0) (synCfdmem))) (synWex x
          (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0)))))
      (synWa (.classMem C B) (.classMem D B)) p0008
  have p0010 := @gBiid (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
  have p0011 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem)))
      (synWa (.classMem C B) (.classMem D B)) p0010
  have p0012 := @gSimpl (.classMem C B) (.classMem D B)
  have p0013 := @gElex C B
  have p0014 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem C B)
      (.classMem C (synCvv)) p0012 p0013
  have p0015 := @gSimpr (.classMem C B) (.classMem D B)
  have p0016 := @gElex D B
  have p0017 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem D B)
      (.classMem D (synCvv)) p0015 p0016
  have p0018 :=
    @gJca (synWa (.classMem C B) (.classMem D B)) (.classMem C (synCvv))
      (.classMem D (synCvv)) p0014 p0017
  have p0019 := @gFdprj0valV x C D dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0020 :=
    @gSyl (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
        (.classEq (.cv x) (synCsn (synCsn C))))
      p0018 p0019
  have p0021 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))
      (.classEq (.cv x) (synCsn (synCsn C))) p0011 p0020
  have p0022 :=
    @gExbidv (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0)))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classEq (.cv x) (synCsn (synCsn C))))
      x dv_cache_0008 p0021
  have p0023 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj0) (synCfdmem)))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj0))))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classEq (.cv x) (synCsn (synCsn C)))))
      p0009 p0022
  have p0024 :=
    @gAncom (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classEq (.cv x) (synCsn (synCsn C)))
  have p0025 :=
    @gA1i
      (synWb (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classEq (.cv x) (synCsn (synCsn C))))
        (synWa (.classEq (.cv x) (synCsn (synCsn C)))
          (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
      (synWa (.classMem C B) (.classMem D B)) p0024
  have p0026 :=
    @gExbidv (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classEq (.cv x) (synCsn (synCsn C))))
      (synWa (.classEq (.cv x) (synCsn (synCsn C)))
        (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem)))
      x dv_cache_0008 p0025
  have p0027 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj0) (synCfdmem)))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classEq (.cv x) (synCsn (synCsn C)))))
      (synWex x (synWa (.classEq (.cv x) (synCsn (synCsn C)))
          (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
      p0023 p0026
  have p0028 := @gSnex (synCsn C)
  have p0029 := @gOpkeq2 (.cv x) (synCsn (synCsn C)) (synCsn (.cv e))
  have p0030 :=
    @gEleq1d (.classEq (.cv x) (synCsn (synCsn C)))
      (synCopk (synCsn (.cv e)) (.cv x))
      (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem) p0029
  have p0031 :=
    @gCeqsexgv (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem)) x
      (synCsn (synCsn C)) (synCvv) dv_cache_0009 dv_cache_0010 p0030
  have p0032 := Nominal.mp p0028 p0031
  have p0033 :=
    @gA1i
      (synWb (synWex x (synWa (.classEq (.cv x) (synCsn (synCsn C)))
            (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
        (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem)))
      (synWa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj0) (synCfdmem)))
      (synWex x (synWa (.classEq (.cv x) (synCsn (synCsn C)))
          (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem)) p0027
      p0033
  have p0036 := @gFdmemvalC B C e
  have p0037 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem C B)
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
        (.classMem C (.cv e)))
      p0012 p0036
  have p0038 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj0) (synCfdmem)))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn C))) (synCfdmem))
      (.classMem C (.cv e)) p0034 p0037
  have p0039 := (Nominal.classEqRefl (synCfddom A B))
  have p0040 :=
    @gEleq2i (synCfddom A B) (synCxpk (synCpw1 A) (synCxpk B B))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0039
  have p0041 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCxpk (synCpw1 A) (synCxpk B B))))
      (synWa (.classMem C B) (.classMem D B)) p0040
  have p0044 :=
    @gOpkelxpk (synCsn (.cv e)) (synCopk C D) (synCpw1 A) (synCxpk B B) p0006 p0007
  have p0045 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCxpk (synCpw1 A) (synCxpk B B)))
        (synWa (.classMem (synCsn (.cv e)) (synCpw1 A))
          (.classMem (synCopk C D) (synCxpk B B))))
      (synWa (.classMem C B) (.classMem D B)) p0044
  have p0046 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCxpk (synCpw1 A) (synCxpk B B)))
      (synWa (.classMem (synCsn (.cv e)) (synCpw1 A))
        (.classMem (synCopk C D) (synCxpk B B)))
      p0041 p0045
  have p0047 := @gSnelpw1 (.cv e) A
  have p0048 :=
    @gA1i (synWb (.classMem (synCsn (.cv e)) (synCpw1 A)) (.classMem (.cv e) A))
      (synWa (.classMem C B) (.classMem D B)) p0047
  have p0056 := @gOpkelxpkg C D B B (synCvv) (synCvv)
  have p0057 :=
    @gSyl (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWb (.classMem (synCopk C D) (synCxpk B B))
        (synWa (.classMem C B) (.classMem D B)))
      p0018 p0056
  have p0058 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCsn (.cv e)) (synCpw1 A)) (.classMem (.cv e) A)
      (.classMem (synCopk C D) (synCxpk B B)) (synWa (.classMem C B) (.classMem D B))
      p0048 p0057
  have p0059 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (synWa (.classMem (synCsn (.cv e)) (synCpw1 A))
        (.classMem (synCopk C D) (synCxpk B B)))
      (synWa (.classMem (.cv e) A) (synWa (.classMem C B) (.classMem D B))) p0046 p0058
  have p0060 := @gIba (synWa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
  have p0061 :=
    @gBicomd (synWa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
      (synWa (.classMem (.cv e) A) (synWa (.classMem C B) (.classMem D B))) p0060
  have p0062 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (synWa (.classMem (.cv e) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (.cv e) A) p0059 p0061
  have p0063 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj0) (synCfdmem)))
      (.classMem C (.cv e))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (.classMem (.cv e) A) p0038 p0062
  have p0064 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCcomk (synCfdprj0) (synCfdmem)))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B)))
      (synWa (.classMem C (.cv e)) (.classMem (.cv e) A)) p0005 p0063
  have p0065 := @gAncom (.classMem C (.cv e)) (.classMem (.cv e) A)
  have p0066 :=
    @gA1i
      (synWb (synWa (.classMem C (.cv e)) (.classMem (.cv e) A))
        (synWa (.classMem (.cv e) A) (.classMem C (.cv e))))
      (synWa (.classMem C B) (.classMem D B)) p0065
  have p0067 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
      (synWa (.classMem C (.cv e)) (.classMem (.cv e) A))
      (synWa (.classMem (.cv e) A) (.classMem C (.cv e))) p0064 p0066
  exact p0067


end NFChoice.DirectNominalPrf.WPPReplay

end
