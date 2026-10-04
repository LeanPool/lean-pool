/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.WellOrderPullbackBlock001
public import LeanPool.NFWeakPartition.Certificates.WellOrderPullbackBlock002
public import LeanPool.NFWeakPartition.ReplaySupport.WellOrderPullback6

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pwpullwesetimpndv`. -/
@[expose]
noncomputable def gPwpullwesetimpndv (x : Var) (y : Var) (f : Var) (r : Var)
    (_dv_f_r : f ≠ r) (_dv_f_x : f ≠ x) (_dv_f_y : f ≠ y) (_dv_r_x : r ≠ x)
    (_dv_r_y : r ≠ y) (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x))) :=
  by
  exact
    (gPwpullwesetimpndvStage1 x y f r
      (fun p0000 p0004 p0015 p0018 p0022 p0027 p0036 p0038 p0039 p0042 p0045 p0046 p0047
          p0049 p0050 p0055 p0058 p0059 p0066 p0081 p0082 p0090 p0101 p0102 p0113 p0114
          p0115 p0116 p0117 p0126 p0130 p0132 p0134 p0135 p0137 p0140 p0141 p0162 p0165
          p0169 p0172 p0185 p0190 p0193 p0195 p0201 p0202 p0212 p0277 p0278 p0282 p0283
          p0286 p0289 p0290 p0293 p0294 =>
        (gPwpullwesetimpndvStage2 x y f r p0000 p0004 p0018 p0022 p0027 p0036 p0039
          p0045 p0047 p0050 p0055 p0059 p0066 p0082 p0090 p0102 p0115 p0117 p0130 p0132
          p0134 p0135 p0137 p0140 p0141 p0162 p0165 p0169 p0172 p0185 p0190 p0193 p0195
          p0201 p0202 p0212 p0278 p0282 p0283 p0289 p0290 p0293 p0294
          (fun p0318 p0331 p0335 p0437 p0440 p0452 p0517 p0537 p0538 p0556 p0561 p0574 p0581 =>
            (gPwpullwesetimpndvStage3 x y f r p0000 p0004 p0022 p0027 p0042 p0046 p0101
              p0113 p0115 p0116 p0117 p0126 p0277 p0318 p0331 p0335 p0437 p0452 p0517
              p0537 p0538 p0556 p0561 p0574 p0581
              (fun p0607 p0615 p0687 p0690 p0693 p0694 p0696 p0709 p0766 p0769 p0770 p0776
                  p0777 p0780 p0782 p0801 p0802 p0807 p0811 p0812 =>
                (gPwpullwesetimpndvStage4 x y f r p0015 p0042 p0286 p0615 p0766 p0769
                  p0770 p0776 p0780 p0782 p0801 p0802 p0807 p0811 p0812
                  (fun p0854 p0978 p0984 p0992 p0994 p0995 p0997 p1000 =>
                    (gPwpullwesetimpndvStage5 x y f r p0000 p0036 p0038 p0039 p0042
                      p0045 p0047 p0049 p0050 p0055 p0058 p0081 p0101 p0114 p0117 p0162
                      p0169 p0185 p0193 p0201 p0318 p0709 p0854 p0978 p0984 p0992 p0994
                      p0995 p0997 p1000 (fun p1293 p1294 p1299 =>
                        (gPwpullwesetimpndvStage6 x y f r p0000 p0115 p0117 p0440 p0607
                          p0687 p0690 p0693 p0694 p0696 p0777 p1293 p1294 p1299
                          (fun p1476 => p1476))))))))))))

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pwpullssxpsetimpndv`. -/
@[expose]
noncomputable def gPwpullssxpsetimpndv (x : Var) (y : Var) (f : Var) (r : Var)
    (_dv_f_r : f ≠ r) (_dv_f_x : f ≠ x) (_dv_f_y : f ≠ y) (_dv_r_x : r ≠ x)
    (_dv_r_y : r ≠ y) (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWfo (.cv f) (.cv x) (.cv y))
        (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x)))) :=
  by
  have p0000 := @gSsdmrn (synCpwpull (.cv f) (.cv r))
  have p0001 := (Nominal.classEqRefl (synCpwpull (.cv f) (.cv r)))
  have p0002 :=
    @gDmeqi (synCpwpull (.cv f) (.cv r))
      (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0001
  have p0003 := @gDmcoss (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)
  have p0004 :=
    @gEqsstri (synCdm (synCpwpull (.cv f) (.cv r)))
      (synCdm (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f))) (synCdm (.cv f))
      p0002 p0003
  have p0005 := @gFofn (.cv x) (.cv y) (.cv f)
  have p0006 := @gId (synWfo (.cv f) (.cv x) (.cv y))
  have p0007 :=
    @gA1ii (.imp (synWfo (.cv f) (.cv x) (.cv y)) (synWfn (.cv f) (.cv x)))
      (.imp (synWfo (.cv f) (.cv x) (.cv y)) (synWfo (.cv f) (.cv x) (.cv y))) p0005
      p0006
  have p0008 := @gFndm (.cv x) (.cv f)
  have p0009 :=
    @gSyl (synWfo (.cv f) (.cv x) (.cv y)) (synWfn (.cv f) (.cv x))
      (.classEq (synCdm (.cv f)) (.cv x)) p0007 p0008
  have p0010 :=
    @gSyl5sseq (synWfo (.cv f) (.cv x) (.cv y)) (synCdm (.cv f))
      (synCdm (synCpwpull (.cv f) (.cv r))) (.cv x) p0004 p0009
  have p0012 :=
    @gRneqi (synCpwpull (.cv f) (.cv r))
      (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0001
  have p0013 := @gRncoss (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)
  have p0014 :=
    @gEqsstri (synCrn (synCpwpull (.cv f) (.cv r)))
      (synCrn (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)))
      (synCrn (synCcom (synCcnv (.cv f)) (.cv r))) p0012 p0013
  have p0015 := @gRncoss (synCcnv (.cv f)) (.cv r)
  have p0016 :=
    @gSstri (synCrn (synCpwpull (.cv f) (.cv r)))
      (synCrn (synCcom (synCcnv (.cv f)) (.cv r))) (synCrn (synCcnv (.cv f))) p0014
      p0015
  have p0017 := @gDfrn4 (synCcnv (.cv f))
  have p0018 := @gCnvcnv (.cv f)
  have p0019 := @gDmeqi (synCcnv (synCcnv (.cv f))) (.cv f) p0018
  have p0020 :=
    @gEqtri (synCrn (synCcnv (.cv f))) (synCdm (synCcnv (synCcnv (.cv f))))
      (synCdm (.cv f)) p0017 p0019
  have p0021 :=
    @gSseqtri (synCrn (synCpwpull (.cv f) (.cv r))) (synCrn (synCcnv (.cv f)))
      (synCdm (.cv f)) p0016 p0020
  have p0022 :=
    @gSyl5sseq (synWfo (.cv f) (.cv x) (.cv y)) (synCdm (.cv f))
      (synCrn (synCpwpull (.cv f) (.cv r))) (.cv x) p0021 p0009
  have p0023 :=
    @gJca (synWfo (.cv f) (.cv x) (.cv y))
      (synWss (synCdm (synCpwpull (.cv f) (.cv r))) (.cv x))
      (synWss (synCrn (synCpwpull (.cv f) (.cv r))) (.cv x)) p0010 p0022
  have p0024 :=
    @gXpss12 (synCdm (synCpwpull (.cv f) (.cv r))) (.cv x)
      (synCrn (synCpwpull (.cv f) (.cv r))) (.cv x)
  have p0025 :=
    @gSyl (synWfo (.cv f) (.cv x) (.cv y))
      (synWa (synWss (synCdm (synCpwpull (.cv f) (.cv r))) (.cv x))
        (synWss (synCrn (synCpwpull (.cv f) (.cv r))) (.cv x)))
      (synWss (synCxp (synCdm (synCpwpull (.cv f) (.cv r)))
          (synCrn (synCpwpull (.cv f) (.cv r)))) (synCxp (.cv x) (.cv x)))
      p0023 p0024
  have p0026 :=
    @gSyl5ss (synWfo (.cv f) (.cv x) (.cv y)) (synCpwpull (.cv f) (.cv r))
      (synCxp (synCdm (synCpwpull (.cv f) (.cv r))) (synCrn (synCpwpull (.cv f) (.cv r))))
      (synCxp (.cv x) (.cv x)) p0000 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_elhwcodesclndv`. -/
@[expose]
noncomputable def gElhwcodesclndv (B : Class) (C : Class) (D : Class)
    (hyp_elhwcodesclndv_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_elhwcodesclndv_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop B C) (synChwcodes D))
        (synWa (synWbr B (synCwe) C) (synWss C D))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (D).fv ((Class.cv r)).fv := by
    exact
      (show Disjoint (D).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((D).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (D).fv from (by exact fresh_r_not_D))))))
  have dv_cache_0002 : r ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_B, not_false_eq_true])
  have dv_cache_0003 :
    r ∉
      ((synWb (.classMem (synCop B C) (synChwcodes D))
          (synWa (synWbr B (synCwe) C) (synWss C D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_r_not_B, fresh_r_not_C, fresh_r_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classEq (.cv r) B)
  have p0001 := @gOpeq1d (.classEq (.cv r) B) (.cv r) B C p0000
  have p0002 :=
    @gEleq1d (.classEq (.cv r) B) (synCop (.cv r) C) (synCop B C) (synChwcodes D)
      p0001
  have p0004 := @gBreq1d (.classEq (.cv r) B) (.cv r) B C (synCwe) p0000
  have p0005 := @gBiid (synWss C D)
  have p0006 := @gA1i (synWb (synWss C D) (synWss C D)) (.classEq (.cv r) B) p0005
  have p0007 :=
    @gAnbi12d (.classEq (.cv r) B) (synWbr (.cv r) (synCwe) C) (synWbr B (synCwe) C)
      (synWss C D) (synWss C D) p0004 p0006
  have p0008 :=
    @gBibi12d (.classEq (.cv r) B) (.classMem (synCop (.cv r) C) (synChwcodes D))
      (.classMem (synCop B C) (synChwcodes D))
      (synWa (synWbr (.cv r) (synCwe) C) (synWss C D))
      (synWa (synWbr B (synCwe) C) (synWss C D)) p0002 p0007
  have p0009 := @gVex r
  have p0010 := @gElhwcodes D C (.cv r) dv_cache_0001 p0009 hyp_elhwcodesclndv_2
  have p0011 :=
    @gVtocl
      (synWb (.classMem (synCop (.cv r) C) (synChwcodes D))
        (synWa (synWbr (.cv r) (synCwe) C) (synWss C D)))
      (synWb (.classMem (synCop B C) (synChwcodes D))
        (synWa (synWbr B (synCwe) C) (synWss C D)))
      r B dv_cache_0002 dv_cache_0003 hyp_elhwcodesclndv_1 p0008 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_hwbijf1oclndv`. -/
@[expose]
noncomputable def gHwbijf1oclndv (B : Class)
    (hyp_hwbijf1oclndv_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem B (synChwbij)) (synWf1o B (synCdm B) (synCrn B))) :=
  by
  let proofSupport : Finset Var := B.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (h)
  have dv_cache_0001 : f ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0002 :
    f ∉ ((synWb (.classMem B (synChwbij)) (synWf1o B (synCdm B) (synCrn B)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          fresh_f_not_B, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gId (.classEq (.cv f) B)
  have p0001 := @gEleq1d (.classEq (.cv f) B) (.cv f) B (synChwbij) p0000
  have p0002 := @gF1oeq1 (synCdm (.cv f)) (synCrn (.cv f)) (.cv f) B
  have p0004 := @gDmeqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0006 := @gRneqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0007 :=
    @gJca (.classEq (.cv f) B) (.classEq (synCdm (.cv f)) (synCdm B))
      (.classEq (synCrn (.cv f)) (synCrn B)) p0004 p0006
  have p0008 := @gF1oeq23 (synCdm (.cv f)) (synCdm B) (synCrn (.cv f)) (synCrn B) B
  have p0009 :=
    @gSyl (.classEq (.cv f) B)
      (synWa (.classEq (synCdm (.cv f)) (synCdm B)) (.classEq (synCrn (.cv f)) (synCrn B)))
      (synWb (synWf1o B (synCdm (.cv f)) (synCrn (.cv f)))
        (synWf1o B (synCdm B) (synCrn B)))
      p0007 p0008
  have p0010 :=
    @gBitrd (.classEq (.cv f) B) (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o B (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o B (synCdm B) (synCrn B)) p0002 p0009
  have p0011 :=
    @gBibi12d (.classEq (.cv f) B) (.classMem (.cv f) (synChwbij))
      (.classMem B (synChwbij)) (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o B (synCdm B) (synCrn B)) p0001 p0010
  have p0012 := @gHwbijf1o f
  have p0013 :=
    @gVtoclg
      (synWb (.classMem (.cv f) (synChwbij))
        (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))))
      (synWb (.classMem B (synChwbij)) (synWf1o B (synCdm B) (synCrn B))) f B
      (synCvv) dv_cache_0001 dv_cache_0002 p0011 p0012
  have p0014 := Nominal.mp hyp_hwbijf1oclndv_1 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodetrncndndv`. -/
@[expose]
noncomputable def gHncodetrncndndv (u : Var) (D : Class) (E : Class) (F : Class)
    (hyp_hncodetrncndndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hncodetrncndndv_2 : Nominal.NPrf (synWf1o F D E)) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn D))
        (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ D.fv ∪ E.fv ∪ F.fv
  let r : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r_ne_y : r ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_ne_x : r ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_f : r ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_r : f ≠ r := Ne.symm fresh_r_ne_f
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have dv_cache_0001 : f ≠ r := by exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0002 : f ≠ x := by
    clear dv_cache_0001
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0003 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0004 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0005 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : f ∉ ((synCcnv (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 :
    f ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x)
              (.cv y)) (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCwe) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u,
          fresh_f_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCrn (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
            (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synCdm (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    y ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWbr (.cv r) (synCwe)
              (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : r ∉ ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    r ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
            (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
              (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCfv (synC1st) (.cv u)))
            (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    f ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
          (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCxp (.cv x) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u,
          fresh_f_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    x ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    y ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 :
    r ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCfv (synC1st) (.cv u)))
            (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @gVex u
  have p0001 := @gHncodetrnfnvalndv u F hyp_hncodetrncndndv_1 p0000
  have p0002 :=
    (Nominal.classEqRefl (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u))))
  have p0003 := @gCnvcnv (synCres F (synCfv (synC2nd) (.cv u)))
  have p0004 :=
    @gCoeq1i (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)) p0003
  have p0005 :=
    @gCoeq1i
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCfv (synC1st) (.cv u)))
      (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0004
  have p0006 :=
    @gEqtri
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCcom (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0002 p0005
  have p0007 := @gHwcnpair u D
  have p0008 := @gId (.classMem (.cv u) (synChwcn D))
  have p0009 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D)) (.classEq (.cv u)
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0007
      p0008
  have p0011 := @gElhwcncl D (.cv u)
  have p0012 := Nominal.mp p0000 p0011
  have p0013 :=
    @gBiimpi (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcodes D)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0012
  have p0014 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D)) (synWa (.classMem (.cv u) (synChwcodes D))
          (synWss (synCfv (synC1st) (.cv u))
            (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0013
      p0008
  have p0015 :=
    @gSimpl (.classMem (.cv u) (synChwcodes D))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
  have p0016 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcodes D)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcodes D)) p0014 p0015
  have p0017 :=
    @gEqeltrrd (.classMem (.cv u) (synChwcn D)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (synChwcodes D)
      p0009 p0016
  have p0018 := @gFvex (.cv u) (synC1st)
  have p0019 := @gFvex (.cv u) (synC2nd)
  have p0020 :=
    @gElhwcodesclndv (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) D p0018
      p0019
  have p0021 :=
    @gSylib (.classMem (.cv u) (synChwcn D))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      p0017 p0020
  have p0022 :=
    @gSimpr (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) D)
  have p0023 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      (synWss (synCfv (synC2nd) (.cv u)) D) p0021 p0022
  have p0024 := @gF1of1 D E F
  have p0025 := Nominal.mp hyp_hncodetrncndndv_2 p0024
  have p0026 :=
    @gJctil (.classMem (.cv u) (synChwcn D)) (synWss (synCfv (synC2nd) (.cv u)) D)
      (synWf1 F D E) p0023 p0025
  have p0027 := @gF1ores D E (synCfv (synC2nd) (.cv u)) F
  have p0028 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWf1 F D E) (synWss (synCfv (synC2nd) (.cv u)) D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      p0026 p0027
  have p0029 :=
    @gF1odm (synCfv (synC2nd) (.cv u)) (synCima F (synCfv (synC2nd) (.cv u)))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0030 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (.classEq (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u)))
      p0028 p0029
  have p0031 :=
    @gEqcomd (.classMem (.cv u) (synChwcn D))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      p0030
  have p0032 :=
    @gF1ofo (synCfv (synC2nd) (.cv u)) (synCima F (synCfv (synC2nd) (.cv u)))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0033 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (synWfo (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      p0028 p0032
  have p0034 :=
    @gForn (synCfv (synC2nd) (.cv u)) (synCima F (synCfv (synC2nd) (.cv u)))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0035 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWfo (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (.classEq (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCima F (synCfv (synC2nd) (.cv u))))
      p0033 p0034
  have p0036 :=
    @gEqcomd (.classMem (.cv u) (synChwcn D))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCima F (synCfv (synC2nd) (.cv u))) p0035
  have p0037 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synC2nd) (.cv u))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCima F (synCfv (synC2nd) (.cv u)))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0031 p0036
  have p0038 :=
    @gF1oeq23 (synCfv (synC2nd) (.cv u))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCima F (synCfv (synC2nd) (.cv u)))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0039 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classEq (synCfv (synC2nd) (.cv u))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (.classEq (synCima F (synCfv (synC2nd) (.cv u)))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWb (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
          (synCima F (synCfv (synC2nd) (.cv u))))
        (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0037 p0038
  have p0040 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0028 p0039
  have p0041 :=
    @gF1ocnv (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0042 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0040 p0041
  have p0043 :=
    @gSimpl (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) D)
  have p0044 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0021
      p0043
  have p0045 :=
    @gBreq2d (.classMem (.cv u) (synChwcn D))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) (synCwe) p0030
  have p0046 :=
    @gMpbird (.classMem (.cv u) (synChwcn D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0044
      p0045
  have p0047 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0042 p0046
  have p0049 :=
    @gBiid
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0050 :=
    @gA1i
      (synWb (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0049
  have p0051 := @gId (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
  have p0052 :=
    @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
      (synCfv (synC1st) (.cv u)) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCwe) p0051
  have p0053 :=
    @gAnbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0050 p0052
  have p0055 :=
    @gCoeq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
      (synCfv (synC1st) (.cv u))
      (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) p0051
  have p0056 :=
    @gCoeq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0055
  have p0057 :=
    (Nominal.classEqRefl
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)))
  have p0058 :=
    @gEqcomi (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCcom
        (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0057
  have p0060 :=
    @gEqcomi
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCcom (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0002
  have p0061 :=
    @gN3eqtr3g (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCcom
        (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      p0056 p0058 p0060
  have p0062 :=
    @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (synCwe) p0061
  have p0063 :=
    @gImbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0053 p0062
  have p0065 := @gResex F (synCfv (synC2nd) (.cv u)) hyp_hncodetrncndndv_1 p0019
  have p0066 := @gDmex (synCres F (synCfv (synC2nd) (.cv u))) p0065
  have p0067 :=
    @gF1oeq3 (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0068 :=
    @gId (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0069 :=
    @gBreq2d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r) (synCwe) p0068
  have p0070 :=
    @gAnbi12d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv r) (synCwe) (.cv y))
      (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0067 p0069
  have p0071 :=
    @gBiid
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0072 :=
    @gA1i
      (synWb (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) p0071
  have p0073 :=
    @gImbi12d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0070 p0072
  have p0076 := @gRnex (synCres F (synCfv (synC2nd) (.cv u))) p0065
  have p0077 :=
    @gF1oeq2 (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0078 := @gBiid (synWbr (.cv r) (synCwe) (.cv y))
  have p0079 :=
    @gA1i
      (synWb (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
      (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) p0078
  have p0080 :=
    @gAnbi12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)) p0077 p0079
  have p0081 :=
    @gId (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0082 :=
    @gBreq2d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) (synCwe)
      p0081
  have p0083 :=
    @gImbi12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (.cv x))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0080 p0082
  have p0086 := @gCnvex (synCres F (synCfv (synC2nd) (.cv u))) p0065
  have p0087 :=
    @gF1oeq1 (.cv x) (.cv y) (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0089 :=
    @gA1i
      (synWb (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
      (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) p0078
  have p0090 :=
    @gAnbi12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (.cv f) (.cv x) (.cv y))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)) p0087 p0089
  have p0091 :=
    @gId (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0092 :=
    @gCnveqd (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0091
  have p0093 :=
    @gCoeq1d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcnv (.cv f)) (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv r) p0092
  have p0095 :=
    @gCoeq12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom (synCcnv (.cv f)) (.cv r))
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
      (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0093 p0091
  have p0096 := (Nominal.classEqRefl (synCpwpull (.cv f) (.cv r)))
  have p0097 :=
    @gEqcomi (synCpwpull (.cv f) (.cv r))
      (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0096
  have p0100 :=
    @gN3eqtr3g (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f))
      (synCcom
        (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (.cv f) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) p0095
      p0097 p0058
  have p0101 :=
    @gBreq1d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (.cv f) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) (.cv x)
      (synCwe) p0100
  have p0102 :=
    @gImbi12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (.cv x))
      p0090 p0101
  have p0103 :=
    @gPwpullwesetimpndv x y f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0104 :=
    @gVtocl
      (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x)))
      (.imp (synWa
          (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (.cv x)))
      f (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0007 dv_cache_0008
      p0086 p0102 p0103
  have p0105 :=
    @gVtocl
      (.imp (synWa
          (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (.cv x)))
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      x (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0009 dv_cache_0010
      p0076 p0083 p0104
  have p0106 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
          (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
        (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      y (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0011 dv_cache_0012
      p0066 p0073 p0105
  have p0107 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
          (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
        (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
          (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCfv (synC1st) (.cv u)))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      r (synCfv (synC1st) (.cv u)) dv_cache_0013 dv_cache_0014 p0018 p0063 p0106
  have p0108 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0047 p0107
  have p0109 :=
    @gSyl5eqbrr (.classMem (.cv u) (synChwcn D))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (synCwe) p0006 p0108
  have p0110 := @gImassrn F (synCfv (synC2nd) (.cv u))
  have p0111 := @gF1ofo D E F
  have p0112 := Nominal.mp hyp_hncodetrncndndv_2 p0111
  have p0113 := @gForn D E F
  have p0114 := Nominal.mp p0112 p0113
  have p0115 :=
    @gSseqtri (synCima F (synCfv (synC2nd) (.cv u))) (synCrn F) E p0110 p0114
  have p0116 :=
    @gSyl6eqss (.classMem (.cv u) (synChwcn D))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCima F (synCfv (synC2nd) (.cv u))) E p0035 p0115
  have p0117 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWbr (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) E) p0109 p0116
  have p0121 :=
    @gCoex (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)) p0065
      p0018
  have p0125 :=
    @gCoex
      (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0121 p0086
  have p0129 :=
    @gElhwcodesclndv
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) E p0125 p0076
  have p0130 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWss (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) E))
      (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcodes E))
      p0117 p0129
  have p0136 :=
    @gEqcomi
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0006
  have p0137 :=
    @gF1ofo (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0138 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0042 p0137
  have p0140 :=
    @gBiid
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0141 :=
    @gA1i
      (synWb (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0140
  have p0150 :=
    @gSseq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0061
  have p0151 :=
    @gImbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0141 p0150
  have p0155 :=
    @gFoeq3 (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0156 :=
    @gBiid
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
  have p0157 :=
    @gA1i
      (synWb (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) p0156
  have p0158 :=
    @gImbi12d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0155 p0157
  have p0162 :=
    @gFoeq2 (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0165 :=
    @gXpeq12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x)
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0081 p0081
  have p0166 :=
    @gSseq2d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCxp (.cv x) (.cv x))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) p0165
  have p0167 :=
    @gImbi12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (.cv x) (.cv x)))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0162 p0166
  have p0171 :=
    @gFoeq1 (.cv x) (.cv y) (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0182 :=
    @gSseq1d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (.cv f) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCxp (.cv x) (.cv x)) p0100
  have p0183 :=
    @gImbi12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (.cv f) (.cv x) (.cv y))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x)))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (.cv x) (.cv x)))
      p0171 p0182
  have p0184 :=
    @gPwpullssxpsetimpndv x y f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0185 :=
    @gVtocl
      (.imp (synWfo (.cv f) (.cv x) (.cv y))
        (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (.cv x) (.cv x))))
      f (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0007 dv_cache_0015
      p0086 p0183 p0184
  have p0186 :=
    @gVtocl
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (.cv x) (.cv x))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      x (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0009 dv_cache_0016
      p0076 p0167 p0185
  have p0187 :=
    @gVtocl
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      y (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0011 dv_cache_0017
      p0066 p0158 p0186
  have p0188 :=
    @gVtocl
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCfv (synC1st) (.cv u)))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      r (synCfv (synC1st) (.cv u)) dv_cache_0013 dv_cache_0018 p0018 p0151 p0187
  have p0189 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0138 p0188
  have p0190 :=
    @gSyl5eqss (.classMem (.cv u) (synChwcn D))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0136 p0189
  have p0202 :=
    @gOpfv1st
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0125 p0076
  have p0214 :=
    @gOpfv2nd
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0125 p0076
  have p0227 :=
    @gXpeq12i
      (synCfv (synC2nd) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0214 p0214
  have p0228 :=
    @gSseq12i
      (synCfv (synC1st) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCxp (synCfv (synC2nd) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd) (synCop
            (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0202 p0227
  have p0229 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWss (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWss (synCfv (synC1st) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCxp (synCfv (synC2nd)
            (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd) (synCop
              (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))))
      p0190 p0228
  have p0230 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcodes E))
      (synWss (synCfv (synC1st) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCxp (synCfv (synC2nd)
            (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd) (synCop
              (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))))
      p0130 p0229
  have p0242 :=
    @gOpex
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0125 p0076
  have p0243 :=
    @gElhwcncl E
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0244 := Nominal.mp p0242 p0243
  have p0245 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcodes E)) (synWss
          (synCfv (synC1st) (synCop (synCcom
                (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCxp (synCfv (synC2nd)
              (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                    (synCfv (synC1st) (.cv u)))
                  (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
                (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd)
              (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                    (synCfv (synC1st) (.cv u)))
                  (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
                (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))))
      (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcn E))
      p0230 p0244
  have p0246 :=
    @gSyl5eqel (.classMem (.cv u) (synChwcn D)) (synCfv (synChncodetrnfn F) (.cv u))
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synChwcn E) p0001 p0245
  exact p0246


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part054`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnqinctrnvaldndv`. -/
@[expose]
noncomputable def gHnqinctrnvaldndv (u : Var) (A : Class) (D : Class) (E : Class)
    (F : Class) (hyp_hnqinctrnvaldndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hnqinctrnvaldndv_2 : Nominal.NPrf (synWf1o F D E))
    (hyp_hnqinctrnvaldndv_3 : Nominal.NPrf (synWss D A))
    (hyp_hnqinctrnvaldndv_4 : Nominal.NPrf (synWss E A))
    (hyp_hnqinctrnvaldndv_5 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn D))
        (.classEq (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D)))
          (synCfv (synChnqinc E A)
            (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let f : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_not_F : v ∉ F.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_r : f ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_f : r ≠ f := Ne.symm fresh_f_ne_r
  have fresh_f_ne_y : f ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_v : f ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_f : v ≠ f := Ne.symm fresh_f_ne_v
  have fresh_r_ne_y : r ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_ne_v : r ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_r : v ≠ r := Ne.symm fresh_r_ne_v
  have dv_cache_0001 : x ∉ ((synCsn (.cv u))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_u,
          not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((synWa (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D))
            (synCsn (.cv u))) (synWbr (synCsn (.cv u)) (synChnqmap1 A)
            (synCec (.cv u) (synChwniso A))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_D, fresh_x_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCec (.cv u) (synChwniso D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCec (.cv u) (synChwniso A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synChnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCcnv (synChnqmap1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_x_not_D,
          not_false_eq_true])
  have dv_cache_0007 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0008 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0009 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0010 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : f ∉ ((synCcnv (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 :
    f ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x)
              (.cv y)) (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCwe) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u,
          fresh_f_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCrn (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0016 :
    x ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
            (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((synCdm (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    y ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWbr (.cv r) (synCwe)
              (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : r ∉ ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 :
    r ∉
      ((Wff.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
            (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
              (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))) (synWbr
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCfv (synC1st) (.cv u)))
            (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0021 :
    f ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
          (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCxp (.cv x) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_not_F, fresh_f_ne_u,
          fresh_f_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 :
    x ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_F, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 :
    y ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
            (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_ne_u, fresh_y_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 :
    r ∉
      ((Wff.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
            (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
              (synCfv (synC1st) (.cv u)))
            (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0025 : r ∉ ((synCvv)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0026 :
    r ∉
      ((Wff.classEq (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u))))
          (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          Finset.mem_union, Finset.mem_singleton, fresh_r_not_F, fresh_r_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 :
    r ∉ ((Wff.classEq (.cv f) (synCres F (synCfv (synC2nd) (.cv u))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_F, fresh_r_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0028 : f ∉ ((synCres F (synCfv (synC2nd) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_F, fresh_f_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0029 : f ∉ ((synChwbij)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0030 :
    f ∉
      ((synWrex r (synCvv) (.classEq (synCfv (synChwgen)
              (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
            (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_f_not_F,
          fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0031 :
    f ∉ ((Wff.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          Finset.mem_union, Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_u,
          fresh_f_not_F, or_false, not_false_eq_true])
  have dv_cache_0032 :
    r ∉ ((Wff.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          Finset.mem_union, Finset.mem_singleton, fresh_r_ne_v, fresh_r_ne_u,
          fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0033 : f ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0034 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0035 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0036 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0037 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show r ≠ v from (by exact fresh_r_ne_v))
  have dv_cache_0038 : v ∉ ((synCfv (synChncodetrnfn F) (.cv u))).fv :=
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
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_F, or_false, not_false_eq_true])
  have dv_cache_0039 :
    v ∉
      ((synWb (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
          (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
              (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
            (synWrex f (synChwbij) (synWrex r (synCvv)
                (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
                  (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))))).fv :=
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
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_F,
          fresh_v_ne_f, fresh_v_ne_r, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0040 : x ∉ ((synCsn (synCfv (synChncodetrnfn F) (.cv u)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, or_false, not_false_eq_true])
  have dv_cache_0041 :
    x ∉
      ((synWa (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
            (synCcnv (synChnqmap1 E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
          (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
            (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, fresh_x_not_E, fresh_x_not_A,
          or_false, not_false_eq_true])
  have dv_cache_0042 :
    x ∉ ((synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, fresh_x_not_E, or_false,
          not_false_eq_true])
  have dv_cache_0043 :
    x ∉ ((synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_F, fresh_x_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0044 : x ∉ ((synCcnv (synChnqmap1 E))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_x_not_E,
          not_false_eq_true])
  have p0000 := @gF1odm D E F
  have p0001 := Nominal.mp hyp_hnqinctrnvaldndv_2 p0000
  have p0002 := @gDmex F hyp_hnqinctrnvaldndv_1
  have p0003 := @gEqeltrri (synCdm F) D (synCvv) p0001 p0002
  have p0004 := @gHnqmap1valcl D (.cv u) p0003
  have p0005 := @gId (.classMem (.cv u) (synChwcn D))
  have p0006 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D))
        (.classEq (synCfv (synChnqmap1 D) (synCsn (.cv u)))
          (synCec (.cv u) (synChwniso D))))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0004
      p0005
  have p0007 := @gSnelpw1 (.cv u) (synChwcn D)
  have p0008 :=
    @gSylibr (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn D))) p0005 p0007
  have p0009 := @gHnqmap1fn D p0003
  have p0010 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn D)))
      (synWfn (synChnqmap1 D) (synCpw1 (synChwcn D))) p0008 p0009
  have p0011 :=
    @gFnbrfvb (synCpw1 (synChwcn D)) (synCsn (.cv u))
      (synCec (.cv u) (synChwniso D)) (synChnqmap1 D)
  have p0012 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWfn (synChnqmap1 D) (synCpw1 (synChwcn D)))
        (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn D))))
      (synWb (.classEq (synCfv (synChnqmap1 D) (synCsn (.cv u)))
          (synCec (.cv u) (synChwniso D)))
        (synWbr (synCsn (.cv u)) (synChnqmap1 D) (synCec (.cv u) (synChwniso D))))
      p0010 p0011
  have p0013 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 D) (synCsn (.cv u))) (synCec (.cv u) (synChwniso D)))
      (synWbr (synCsn (.cv u)) (synChnqmap1 D) (synCec (.cv u) (synChwniso D))) p0006
      p0012
  have p0014 :=
    @gBrcnv (synCec (.cv u) (synChwniso D)) (synCsn (.cv u)) (synChnqmap1 D)
  have p0015 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWbr (synCsn (.cv u)) (synChnqmap1 D) (synCec (.cv u) (synChwniso D)))
      (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (synCsn (.cv u)))
      p0013 p0014
  have p0016 := @gHwcnssbase A D hyp_hnqinctrnvaldndv_3
  have p0017 := @gSsel (synChwcn D) (synChwcn A) (.cv u)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gA1ii (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn A)))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0018
      p0005
  have p0020 := @gHnqmap1valcl A (.cv u) hyp_hnqinctrnvaldndv_5
  have p0021 :=
    @gSyl (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u))) (synCec (.cv u) (synChwniso A)))
      p0019 p0020
  have p0022 := @gSnelpw1 (.cv u) (synChwcn A)
  have p0023 :=
    @gSylibr (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn A))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A))) p0019 p0022
  have p0024 := @gHnqmap1fn A hyp_hnqinctrnvaldndv_5
  have p0025 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A))) p0023 p0024
  have p0026 :=
    @gFnbrfvb (synCpw1 (synChwcn A)) (synCsn (.cv u))
      (synCec (.cv u) (synChwniso A)) (synChnqmap1 A)
  have p0027 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A)))
        (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A))))
      (synWb (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u)))
          (synCec (.cv u) (synChwniso A)))
        (synWbr (synCsn (.cv u)) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))))
      p0025 p0026
  have p0028 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u))) (synCec (.cv u) (synChwniso A)))
      (synWbr (synCsn (.cv u)) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))) p0021
      p0027
  have p0029 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (synCsn (.cv u)))
      (synWbr (synCsn (.cv u)) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))) p0015
      p0028
  have p0030 := @gSnex (.cv u)
  have p0031 := @gId (.classEq (.cv x) (synCsn (.cv u)))
  have p0032 :=
    @gBreq2d (.classEq (.cv x) (synCsn (.cv u))) (.cv x) (synCsn (.cv u))
      (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) p0031
  have p0034 :=
    @gBreq1d (.classEq (.cv x) (synCsn (.cv u))) (.cv x) (synCsn (.cv u))
      (synCec (.cv u) (synChwniso A)) (synChnqmap1 A) p0031
  have p0035 :=
    @gAnbi12d (.classEq (.cv x) (synCsn (.cv u)))
      (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (.cv x))
      (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (synCsn (.cv u)))
      (synWbr (.cv x) (synChnqmap1 A) (synCec (.cv u) (synChwniso A)))
      (synWbr (synCsn (.cv u)) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))) p0032
      p0034
  have p0036 :=
    @gSpcev
      (synWa (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (.cv x))
        (synWbr (.cv x) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))))
      (synWa (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D))
          (synCsn (.cv u)))
        (synWbr (synCsn (.cv u)) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))))
      x (synCsn (.cv u)) dv_cache_0001 dv_cache_0002 p0030 p0035
  have p0037 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D))
          (synCsn (.cv u)))
        (synWbr (synCsn (.cv u)) (synChnqmap1 A) (synCec (.cv u) (synChwniso A))))
      (synWex x (synWa
          (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (.cv x))
          (synWbr (.cv x) (synChnqmap1 A) (synCec (.cv u) (synChwniso A)))))
      p0029 p0036
  have p0038 :=
    @gBrco x (synCec (.cv u) (synChwniso D)) (synCec (.cv u) (synChwniso A))
      (synChnqmap1 A) (synCcnv (synChnqmap1 D)) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0039 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWex x (synWa
          (synWbr (synCec (.cv u) (synChwniso D)) (synCcnv (synChnqmap1 D)) (.cv x))
          (synWbr (.cv x) (synChnqmap1 A) (synCec (.cv u) (synChwniso A)))))
      (synWbr (synCec (.cv u) (synChwniso D))
        (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
        (synCec (.cv u) (synChwniso A)))
      p0037 p0038
  have p0040 := (Nominal.classEqRefl (synChnqinc D A))
  have p0041 :=
    @gBreqi (synCec (.cv u) (synChwniso D)) (synCec (.cv u) (synChwniso A))
      (synChnqinc D A) (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D))) p0040
  have p0042 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWbr (synCec (.cv u) (synChwniso D))
        (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 D)))
        (synCec (.cv u) (synChwniso A)))
      (synWbr (synCec (.cv u) (synChwniso D)) (synChnqinc D A)
        (synCec (.cv u) (synChwniso A)))
      p0039 p0041
  have p0043 := @gHwnisoclasselhnordcl D (.cv u) p0003
  have p0044 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D))
        (.classMem (synCec (.cv u) (synChwniso D)) (synChnord D)))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0043
      p0005
  have p0045 := @gHnqincfn A D hyp_hnqinctrnvaldndv_3 p0003 hyp_hnqinctrnvaldndv_5
  have p0046 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classMem (synCec (.cv u) (synChwniso D)) (synChnord D))
      (synWfn (synChnqinc D A) (synChnord D)) p0044 p0045
  have p0047 :=
    @gFnbrfvb (synChnord D) (synCec (.cv u) (synChwniso D))
      (synCec (.cv u) (synChwniso A)) (synChnqinc D A)
  have p0048 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWfn (synChnqinc D A) (synChnord D))
        (.classMem (synCec (.cv u) (synChwniso D)) (synChnord D)))
      (synWb (.classEq (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D)))
          (synCec (.cv u) (synChwniso A)))
        (synWbr (synCec (.cv u) (synChwniso D)) (synChnqinc D A)
          (synCec (.cv u) (synChwniso A))))
      p0046 p0047
  have p0049 :=
    @gMpbird (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D)))
        (synCec (.cv u) (synChwniso A)))
      (synWbr (synCec (.cv u) (synChwniso D)) (synChnqinc D A)
        (synCec (.cv u) (synChwniso A)))
      p0042 p0048
  have p0050 := @gSsv D
  have p0051 := @gHwcnssbase (synCvv) D p0050
  have p0052 := @gSsel (synChwcn D) (synChwcn (synCvv)) (.cv u)
  have p0053 := Nominal.mp p0051 p0052
  have p0054 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn (synCvv))))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0053
      p0005
  have p0055 := @gVex u
  have p0056 := @gHncodetrnfnvalndv u F hyp_hnqinctrnvaldndv_1 p0055
  have p0057 :=
    (Nominal.classEqRefl (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u))))
  have p0058 := @gCnvcnv (synCres F (synCfv (synC2nd) (.cv u)))
  have p0059 :=
    @gCoeq1i (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)) p0058
  have p0060 :=
    @gCoeq1i
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCfv (synC1st) (.cv u)))
      (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0059
  have p0061 :=
    @gEqtri
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCcom (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0057 p0060
  have p0062 := @gHwcnpair u D
  have p0063 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D)) (.classEq (.cv u)
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0062
      p0005
  have p0065 := @gElhwcncl D (.cv u)
  have p0066 := Nominal.mp p0055 p0065
  have p0067 :=
    @gBiimpi (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcodes D)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0066
  have p0068 :=
    @gA1ii
      (.imp (.classMem (.cv u) (synChwcn D)) (synWa (.classMem (.cv u) (synChwcodes D))
          (synWss (synCfv (synC1st) (.cv u))
            (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))))
      (.imp (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn D))) p0067
      p0005
  have p0069 :=
    @gSimpl (.classMem (.cv u) (synChwcodes D))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
  have p0070 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcodes D)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcodes D)) p0068 p0069
  have p0071 :=
    @gEqeltrrd (.classMem (.cv u) (synChwcn D)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (synChwcodes D)
      p0063 p0070
  have p0072 := @gFvex (.cv u) (synC1st)
  have p0073 := @gFvex (.cv u) (synC2nd)
  have p0074 :=
    @gElhwcodesclndv (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) D p0072
      p0073
  have p0075 :=
    @gSylib (.classMem (.cv u) (synChwcn D))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      p0071 p0074
  have p0076 :=
    @gSimpr (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) D)
  have p0077 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      (synWss (synCfv (synC2nd) (.cv u)) D) p0075 p0076
  have p0078 := @gF1of1 D E F
  have p0079 := Nominal.mp hyp_hnqinctrnvaldndv_2 p0078
  have p0080 :=
    @gJctil (.classMem (.cv u) (synChwcn D)) (synWss (synCfv (synC2nd) (.cv u)) D)
      (synWf1 F D E) p0077 p0079
  have p0081 := @gF1ores D E (synCfv (synC2nd) (.cv u)) F
  have p0082 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWf1 F D E) (synWss (synCfv (synC2nd) (.cv u)) D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      p0080 p0081
  have p0083 :=
    @gF1odm (synCfv (synC2nd) (.cv u)) (synCima F (synCfv (synC2nd) (.cv u)))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0084 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (.classEq (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u)))
      p0082 p0083
  have p0085 :=
    @gEqcomd (.classMem (.cv u) (synChwcn D))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      p0084
  have p0086 :=
    @gF1ofo (synCfv (synC2nd) (.cv u)) (synCima F (synCfv (synC2nd) (.cv u)))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0087 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (synWfo (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      p0082 p0086
  have p0088 :=
    @gForn (synCfv (synC2nd) (.cv u)) (synCima F (synCfv (synC2nd) (.cv u)))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0089 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWfo (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (.classEq (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCima F (synCfv (synC2nd) (.cv u))))
      p0087 p0088
  have p0090 :=
    @gEqcomd (.classMem (.cv u) (synChwcn D))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCima F (synCfv (synC2nd) (.cv u))) p0089
  have p0091 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synC2nd) (.cv u))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCima F (synCfv (synC2nd) (.cv u)))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0085 p0090
  have p0092 :=
    @gF1oeq23 (synCfv (synC2nd) (.cv u))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCima F (synCfv (synC2nd) (.cv u)))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0093 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classEq (synCfv (synC2nd) (.cv u))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (.classEq (synCima F (synCfv (synC2nd) (.cv u)))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWb (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
          (synCima F (synCfv (synC2nd) (.cv u))))
        (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0091 p0092
  have p0094 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC2nd) (.cv u))
        (synCima F (synCfv (synC2nd) (.cv u))))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0082 p0093
  have p0095 :=
    @gF1ocnv (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCres F (synCfv (synC2nd) (.cv u)))
  have p0096 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0094 p0095
  have p0097 :=
    @gSimpl (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) D)
  have p0098 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0075
      p0097
  have p0099 :=
    @gBreq2d (.classMem (.cv u) (synChwcn D))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) (synCwe) p0084
  have p0100 :=
    @gMpbird (.classMem (.cv u) (synChwcn D))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))) p0098
      p0099
  have p0101 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0096 p0100
  have p0103 :=
    @gBiid
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0104 :=
    @gA1i
      (synWb (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0103
  have p0105 := @gId (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
  have p0106 :=
    @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
      (synCfv (synC1st) (.cv u)) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCwe) p0105
  have p0107 :=
    @gAnbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0104 p0106
  have p0109 :=
    @gCoeq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
      (synCfv (synC1st) (.cv u))
      (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) p0105
  have p0110 :=
    @gCoeq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0109
  have p0111 :=
    (Nominal.classEqRefl
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)))
  have p0112 :=
    @gEqcomi (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCcom
        (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0111
  have p0114 :=
    @gEqcomi
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCcom (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0057
  have p0115 :=
    @gN3eqtr3g (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCcom
        (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      p0110 p0112 p0114
  have p0116 :=
    @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (synCwe) p0115
  have p0117 :=
    @gImbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0107 p0116
  have p0119 := @gResex F (synCfv (synC2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0073
  have p0120 := @gDmex (synCres F (synCfv (synC2nd) (.cv u))) p0119
  have p0121 :=
    @gF1oeq3 (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0122 :=
    @gId (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0123 :=
    @gBreq2d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r) (synCwe) p0122
  have p0124 :=
    @gAnbi12d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv r) (synCwe) (.cv y))
      (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0121 p0123
  have p0125 :=
    @gBiid
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0126 :=
    @gA1i
      (synWb (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) p0125
  have p0127 :=
    @gImbi12d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0124 p0126
  have p0130 := @gRnex (synCres F (synCfv (synC2nd) (.cv u))) p0119
  have p0131 :=
    @gF1oeq2 (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0132 := @gBiid (synWbr (.cv r) (synCwe) (.cv y))
  have p0133 :=
    @gA1i
      (synWb (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
      (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) p0132
  have p0134 :=
    @gAnbi12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)) p0131 p0133
  have p0135 :=
    @gId (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0136 :=
    @gBreq2d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) (synCwe)
      p0135
  have p0137 :=
    @gImbi12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (.cv x))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0134 p0136
  have p0140 := @gCnvex (synCres F (synCfv (synC2nd) (.cv u))) p0119
  have p0141 :=
    @gF1oeq1 (.cv x) (.cv y) (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0143 :=
    @gA1i
      (synWb (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
      (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) p0132
  have p0144 :=
    @gAnbi12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWf1o (.cv f) (.cv x) (.cv y))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)) p0141 p0143
  have p0145 :=
    @gId (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0146 :=
    @gCnveqd (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0145
  have p0147 :=
    @gCoeq1d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcnv (.cv f)) (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv r) p0146
  have p0149 :=
    @gCoeq12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom (synCcnv (.cv f)) (.cv r))
      (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
      (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0147 p0145
  have p0150 := (Nominal.classEqRefl (synCpwpull (.cv f) (.cv r)))
  have p0151 :=
    @gEqcomi (synCpwpull (.cv f) (.cv r))
      (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0150
  have p0154 :=
    @gN3eqtr3g (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f))
      (synCcom
        (synCcom (synCcnv (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))) (.cv r))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (.cv f) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) p0149
      p0151 p0112
  have p0155 :=
    @gBreq1d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (.cv f) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) (.cv x)
      (synCwe) p0154
  have p0156 :=
    @gImbi12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)))
      (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCwe) (.cv x))
      p0144 p0155
  have p0157 :=
    @gPwpullwesetimpndv x y f r dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012
  have p0158 :=
    @gVtocl
      (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x)))
      (.imp (synWa
          (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (.cv x)))
      f (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0013 dv_cache_0014
      p0140 p0156 p0157
  have p0159 :=
    @gVtocl
      (.imp (synWa
          (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (.cv x)))
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      x (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0015 dv_cache_0016
      p0130 p0137 p0158
  have p0160 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
          (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
          (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
        (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      y (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0017 dv_cache_0018
      p0120 p0127 p0159
  have p0161 :=
    @gVtocl
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
          (synWbr (.cv r) (synCwe) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
        (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (.imp (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
          (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
            (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))) (synWbr
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCfv (synC1st) (.cv u)))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      r (synCfv (synC1st) (.cv u)) dv_cache_0019 dv_cache_0020 p0072 p0117 p0160
  have p0162 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWbr (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0101 p0161
  have p0163 :=
    @gSyl5eqbrr (.classMem (.cv u) (synChwcn D))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (synCwe) p0061 p0162
  have p0164 := @gImassrn F (synCfv (synC2nd) (.cv u))
  have p0165 := @gF1ofo D E F
  have p0166 := Nominal.mp hyp_hnqinctrnvaldndv_2 p0165
  have p0167 := @gForn D E F
  have p0168 := Nominal.mp p0166 p0167
  have p0169 :=
    @gSseqtri (synCima F (synCfv (synC2nd) (.cv u))) (synCrn F) E p0164 p0168
  have p0170 :=
    @gSyl6eqss (.classMem (.cv u) (synChwcn D))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCima F (synCfv (synC2nd) (.cv u))) E p0089 p0169
  have p0171 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWbr (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) E) p0163 p0170
  have p0175 :=
    @gCoex (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)) p0119
      p0072
  have p0179 :=
    @gCoex
      (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) p0175 p0140
  have p0183 :=
    @gElhwcodesclndv
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) E p0179 p0130
  have p0184 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCwe) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWss (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) E))
      (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcodes E))
      p0171 p0183
  have p0190 :=
    @gEqcomi
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      p0061
  have p0191 :=
    @gF1ofo (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0192 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      p0096 p0191
  have p0194 :=
    @gBiid
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0195 :=
    @gA1i
      (synWb (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
        (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0194
  have p0204 :=
    @gSseq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0115
  have p0205 :=
    @gImbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0195 p0204
  have p0209 :=
    @gFoeq3 (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0210 :=
    @gBiid
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
  have p0211 :=
    @gA1i
      (synWb (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) p0210
  have p0212 :=
    @gImbi12d (.classEq (.cv y) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0209 p0211
  have p0216 :=
    @gFoeq2 (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)
      (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0219 :=
    @gXpeq12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x)
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0135 p0135
  have p0220 :=
    @gSseq2d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCxp (.cv x) (.cv x))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r)) p0219
  have p0221 :=
    @gImbi12d (.classEq (.cv x) (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (.cv x) (.cv x)))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0216 p0220
  have p0225 :=
    @gFoeq1 (.cv x) (.cv y) (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
  have p0236 :=
    @gSseq1d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (.cv f) (.cv r))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
      (synCxp (.cv x) (.cv x)) p0154
  have p0237 :=
    @gImbi12d (.classEq (.cv f) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWfo (.cv f) (.cv x) (.cv y))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
      (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x)))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
        (synCxp (.cv x) (.cv x)))
      p0225 p0236
  have p0238 :=
    @gPwpullssxpsetimpndv x y f r dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012
  have p0239 :=
    @gVtocl
      (.imp (synWfo (.cv f) (.cv x) (.cv y))
        (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (.cv x) (.cv x))))
      f (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0013 dv_cache_0021
      p0140 p0237 p0238
  have p0240 :=
    @gVtocl
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
        (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (.cv x) (.cv x))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      x (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0015 dv_cache_0022
      p0130 p0221 p0239
  have p0241 :=
    @gVtocl
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      y (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) dv_cache_0017 dv_cache_0023
      p0120 p0212 p0240
  have p0242 :=
    @gVtocl
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))) (.cv r))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (.imp (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synWss
          (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
            (synCfv (synC1st) (.cv u)))
          (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      r (synCfv (synC1st) (.cv u)) dv_cache_0019 dv_cache_0024 p0072 p0205 p0241
  have p0243 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWfo (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synWss (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
          (synCfv (synC1st) (.cv u)))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      p0192 p0242
  have p0244 :=
    @gSyl5eqss (.classMem (.cv u) (synChwcn D))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCpwpull (synCcnv (synCres F (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0190 p0243
  have p0256 :=
    @gOpfv1st
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0179 p0130
  have p0268 :=
    @gOpfv2nd
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0179 p0130
  have p0281 :=
    @gXpeq12i
      (synCfv (synC2nd) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0268 p0268
  have p0282 :=
    @gSseq12i
      (synCfv (synC1st) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCxp (synCfv (synC2nd) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd) (synCop
            (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))
      (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0256 p0281
  have p0283 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWss (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCxp (synCrn (synCres F (synCfv (synC2nd) (.cv u))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synWss (synCfv (synC1st) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCxp (synCfv (synC2nd)
            (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd) (synCop
              (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))))
      p0244 p0282
  have p0284 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcodes E))
      (synWss (synCfv (synC1st) (synCop (synCcom
              (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCxp (synCfv (synC2nd)
            (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd) (synCop
              (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))))
      p0184 p0283
  have p0296 :=
    @gOpex
      (synCcom
        (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
        (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCrn (synCres F (synCfv (synC2nd) (.cv u)))) p0179 p0130
  have p0297 :=
    @gElhwcncl E
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
  have p0298 := Nominal.mp p0296 p0297
  have p0299 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                (synCfv (synC1st) (.cv u)))
              (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
            (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcodes E)) (synWss
          (synCfv (synC1st) (synCop (synCcom
                (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                  (synCfv (synC1st) (.cv u)))
                (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
              (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCxp (synCfv (synC2nd)
              (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                    (synCfv (synC1st) (.cv u)))
                  (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
                (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))) (synCfv (synC2nd)
              (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
                    (synCfv (synC1st) (.cv u)))
                  (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
                (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))))))
      (.classMem (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))) (synChwcn E))
      p0284 p0298
  have p0300 :=
    @gSyl5eqel (.classMem (.cv u) (synChwcn D)) (synCfv (synChncodetrnfn F) (.cv u))
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synChwcn E) p0056 p0299
  have p0301 := @gSsv E
  have p0302 := @gHwcnssbase (synCvv) E p0301
  have p0303 :=
    @gSsel (synChwcn E) (synChwcn (synCvv)) (synCfv (synChncodetrnfn F) (.cv u))
  have p0304 := Nominal.mp p0302 p0303
  have p0305 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))) p0300 p0304
  have p0306 :=
    @gJca (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn (synCvv)))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))) p0054 p0305
  have p0309 := @gHwbijf1oclndv (synCres F (synCfv (synC2nd) (.cv u))) p0119
  have p0310 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWf1o (synCres F (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres F (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (.classMem (synCres F (synCfv (synC2nd) (.cv u))) (synChwbij)) p0094 p0309
  have p0314 :=
    @gHwgenvalclndv (synCres F (synCfv (synC2nd) (.cv u)))
      (synCfv (synC1st) (.cv u)) p0119 p0072
  have p0315 :=
    @gOpeq2d (.classMem (.cv u) (synChwcn D))
      (synCdm (synCres F (synCfv (synC2nd) (.cv u)))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) p0084
  have p0316 :=
    @gEqcomd (.classMem (.cv u) (synChwcn D)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) p0063
  have p0317 :=
    @gEqtrd (.classMem (.cv u) (synChwcn D))
      (synCop (synCfv (synC1st) (.cv u)) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (.cv u) p0315
      p0316
  have p0318 :=
    @gOpeq1d (.classMem (.cv u) (synChwcn D))
      (synCop (synCfv (synC1st) (.cv u)) (synCdm (synCres F (synCfv (synC2nd) (.cv u)))))
      (.cv u)
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0317
  have p0321 :=
    @gEqcomi (synCfv (synChncodetrnfn F) (.cv u))
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      p0056
  have p0322 :=
    @gOpeq2i
      (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))) (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
        (synCrn (synCres F (synCfv (synC2nd) (.cv u)))))
      (synCfv (synChncodetrnfn F) (.cv u)) (.cv u) p0321
  have p0323 :=
    @gSyl6eq (.classMem (.cv u) (synChwcn D))
      (synCop (synCop (synCfv (synC1st) (.cv u))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synCop (synCcom
            (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCop (.cv u) (synCop (synCcom (synCcom (synCres F (synCfv (synC2nd) (.cv u)))
              (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))) p0318 p0322
  have p0324 :=
    @gSyl5eq (.classMem (.cv u) (synChwcn D))
      (synCfv (synChwgen)
        (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))))
      (synCop (synCop (synCfv (synC1st) (.cv u))
          (synCdm (synCres F (synCfv (synC2nd) (.cv u))))) (synCop (synCcom
            (synCcom (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
            (synCcnv (synCres F (synCfv (synC2nd) (.cv u)))))
          (synCrn (synCres F (synCfv (synC2nd) (.cv u))))))
      (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))) p0314 p0323
  have p0326 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))))
        (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))
      (.classMem (synCfv (synC1st) (.cv u)) (synCvv)) p0324 p0072
  have p0328 :=
    @gOpeq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
      (synCfv (synC1st) (.cv u)) (synCres F (synCfv (synC2nd) (.cv u))) p0105
  have p0329 :=
    @gFveq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r))
      (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
      (synChwgen) p0328
  have p0330 :=
    @gEqeq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
      (synCfv (synChwgen)
        (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))))
      (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))) p0329
  have p0331 :=
    @gRspcev
      (.classEq
        (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
        (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))
      (.classEq (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u)))
            (synCfv (synC1st) (.cv u))))
        (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))
      r (synCfv (synC1st) (.cv u)) (synCvv) dv_cache_0019 dv_cache_0025 dv_cache_0026
      p0330
  have p0332 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (synCfv (synC1st) (.cv u)) (synCvv)) (.classEq (synCfv (synChwgen)
            (synCop (synCres F (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))))
          (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))
      (synWrex r (synCvv) (.classEq (synCfv (synChwgen)
            (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
          (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))
      p0326 p0331
  have p0333 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (.classMem (synCres F (synCfv (synC2nd) (.cv u))) (synChwbij))
      (synWrex r (synCvv) (.classEq (synCfv (synChwgen)
            (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
          (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))
      p0310 p0332
  have p0334 := @gId (.classEq (.cv f) (synCres F (synCfv (synC2nd) (.cv u))))
  have p0335 :=
    @gOpeq1d (.classEq (.cv f) (synCres F (synCfv (synC2nd) (.cv u)))) (.cv f)
      (synCres F (synCfv (synC2nd) (.cv u))) (.cv r) p0334
  have p0336 :=
    @gFveq2d (.classEq (.cv f) (synCres F (synCfv (synC2nd) (.cv u))))
      (synCop (.cv f) (.cv r))
      (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)) (synChwgen) p0335
  have p0337 :=
    @gEqeq1d (.classEq (.cv f) (synCres F (synCfv (synC2nd) (.cv u))))
      (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
      (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
      (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))) p0336
  have p0338 :=
    @gRexbidv (.classEq (.cv f) (synCres F (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))
      (.classEq
        (synCfv (synChwgen) (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
        (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))
      r (synCvv) dv_cache_0027 p0337
  have p0339 :=
    @gRspcev
      (synWrex r (synCvv) (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
          (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))
      (synWrex r (synCvv) (.classEq (synCfv (synChwgen)
            (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
          (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))
      f (synCres F (synCfv (synC2nd) (.cv u))) (synChwbij) dv_cache_0028 dv_cache_0029
      dv_cache_0030 p0338
  have p0340 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (synCres F (synCfv (synC2nd) (.cv u))) (synChwbij))
        (synWrex r (synCvv) (.classEq (synCfv (synChwgen)
              (synCop (synCres F (synCfv (synC2nd) (.cv u))) (.cv r)))
            (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))
      p0333 p0339
  have p0341 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))
      p0306 p0340
  have p0342 := @gElex (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))
  have p0343 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv)))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synCvv)) p0305 p0342
  have p0344 := @gId (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))
  have p0345 :=
    @gBreq2d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u))) (.cv v)
      (synCfv (synChncodetrnfn F) (.cv u)) (.cv u) (synChwniso (synCvv)) p0344
  have p0346 := @gBiid (.classMem (.cv u) (synChwcn (synCvv)))
  have p0347 :=
    @gA1i
      (synWb (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (.cv u) (synChwcn (synCvv))))
      (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u))) p0346
  have p0349 :=
    @gEleq1d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u))) (.cv v)
      (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv)) p0344
  have p0350 :=
    @gAnbi12d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))
      (.classMem (.cv u) (synChwcn (synCvv))) (.classMem (.cv u) (synChwcn (synCvv)))
      (.classMem (.cv v) (synChwcn (synCvv)))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))) p0347 p0349
  have p0352 :=
    @gOpeq2d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u))) (.cv v)
      (synCfv (synChncodetrnfn F) (.cv u)) (.cv u) p0344
  have p0353 :=
    @gEqeq2d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))
      (synCop (.cv u) (.cv v)) (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))
      (synCfv (synChwgen) (synCop (.cv f) (.cv r))) p0352
  have p0354 :=
    @gN2rexbidv (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u) (.cv v)))
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))
      f r (synChwbij) (synCvv) dv_cache_0031 dv_cache_0032 p0353
  have p0355 :=
    @gAnbi12d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (.cv v) (synChwcn (synCvv))))
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (.cv v)))))
      (synWrex f (synChwbij) (synWrex r (synCvv)
          (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
            (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))
      p0350 p0354
  have p0356 :=
    @gBibi12d (.classEq (.cv v) (synCfv (synChncodetrnfn F) (.cv u)))
      (synWbr (.cv u) (synChwniso (synCvv)) (.cv v))
      (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
          (.classMem (.cv v) (synChwcn (synCvv)))) (synWrex f (synChwbij)
          (synWrex r (synCvv) (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (.cv v))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
          (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))))
      p0345 p0355
  have p0357 :=
    @gElhwnisogen v u (synCvv) f r dv_cache_0033 dv_cache_0025 dv_cache_0007
      dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
  have p0358 :=
    @gVtoclg
      (synWb (synWbr (.cv u) (synChwniso (synCvv)) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn (synCvv)))
            (.classMem (.cv v) (synChwcn (synCvv)))) (synWrex f (synChwbij)
            (synWrex r (synCvv) (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
                (synCop (.cv u) (.cv v)))))))
      (synWb (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
        (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
            (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
          (synWrex f (synChwbij) (synWrex r (synCvv)
              (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
                (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))))
      v (synCfv (synChncodetrnfn F) (.cv u)) (synCvv) dv_cache_0038 dv_cache_0039 p0356
      p0357
  have p0359 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synCvv))
      (synWb (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
        (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
            (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
          (synWrex f (synChwbij) (synWrex r (synCvv)
              (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
                (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u))))))))
      p0343 p0358
  have p0360 :=
    @gMpbird (.classMem (.cv u) (synChwcn D))
      (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
          (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn (synCvv))))
        (synWrex f (synChwbij) (synWrex r (synCvv)
            (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
              (synCop (.cv u) (synCfv (synChncodetrnfn F) (.cv u)))))))
      p0341 p0359
  have p0361 := @gHwcnssbase A E hyp_hnqinctrnvaldndv_4
  have p0362 := @gSsel (synChwcn E) (synChwcn A) (synCfv (synChncodetrnfn F) (.cv u))
  have p0363 := Nominal.mp p0361 p0362
  have p0364 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A)) p0300 p0363
  have p0365 :=
    @gJca (.classMem (.cv u) (synChwcn D)) (.classMem (.cv u) (synChwcn A))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A)) p0019 p0364
  have p0366 := @gSsv A
  have p0367 :=
    @gHwnisobasebicl (synCvv) (.cv u) (synCfv (synChncodetrnfn F) (.cv u)) A p0366
  have p0368 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
        (synWbr (.cv u) (synChwniso A) (synCfv (synChncodetrnfn F) (.cv u))))
      p0365 p0367
  have p0369 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn F) (.cv u)))
      (synWbr (.cv u) (synChwniso A) (synCfv (synChncodetrnfn F) (.cv u))) p0360 p0368
  have p0370 :=
    @gHwnisoclasseqbcl A (.cv u) (synCfv (synChncodetrnfn F) (.cv u))
      hyp_hnqinctrnvaldndv_5
  have p0371 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A)))
      (synWb (.classEq (synCec (.cv u) (synChwniso A))
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
        (synWbr (.cv u) (synChwniso A) (synCfv (synChncodetrnfn F) (.cv u))))
      p0365 p0370
  have p0372 :=
    @gMpbird (.classMem (.cv u) (synChwcn D))
      (.classEq (synCec (.cv u) (synChwniso A))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      (synWbr (.cv u) (synChwniso A) (synCfv (synChncodetrnfn F) (.cv u))) p0369 p0371
  have p0373 :=
    @gEqtrd (.classMem (.cv u) (synChwcn D))
      (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D)))
      (synCec (.cv u) (synChwniso A))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)) p0049 p0372
  have p0378 := @gRnex F hyp_hnqinctrnvaldndv_1
  have p0379 := @gEqeltrri (synCrn F) E (synCvv) p0168 p0378
  have p0380 := @gHnqmap1valcl E (synCfv (synChncodetrnfn F) (.cv u)) p0379
  have p0381 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))
      (.classEq (synCfv (synChnqmap1 E) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      p0300 p0380
  have p0382 := @gSnelpw1 (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E)
  have p0383 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))
      (.classMem (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synCpw1 (synChwcn E)))
      p0300 p0382
  have p0384 := @gHnqmap1fn E p0379
  have p0385 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classMem (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synCpw1 (synChwcn E)))
      (synWfn (synChnqmap1 E) (synCpw1 (synChwcn E))) p0383 p0384
  have p0386 :=
    @gFnbrfvb (synCpw1 (synChwcn E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u)))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)) (synChnqmap1 E)
  have p0387 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWfn (synChnqmap1 E) (synCpw1 (synChwcn E)))
        (.classMem (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synCpw1 (synChwcn E))))
      (synWb (.classEq
          (synCfv (synChnqmap1 E) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
        (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 E)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))))
      p0385 p0386
  have p0388 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 E) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 E)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      p0381 p0387
  have p0389 :=
    @gBrcnv (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
      (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 E)
  have p0390 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 E)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synCcnv (synChnqmap1 E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
      p0388 p0389
  have p0391 :=
    @gHnqmap1valcl A (synCfv (synChncodetrnfn F) (.cv u)) hyp_hnqinctrnvaldndv_5
  have p0392 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0364 p0391
  have p0393 := @gSnelpw1 (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A)
  have p0394 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn A))
      (.classMem (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synCpw1 (synChwcn A)))
      p0364 p0393
  have p0396 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classMem (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synCpw1 (synChwcn A)))
      (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A))) p0394 p0024
  have p0397 :=
    @gFnbrfvb (synCpw1 (synChwcn A)) (synCsn (synCfv (synChncodetrnfn F) (.cv u)))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)) (synChnqmap1 A)
  have p0398 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A)))
        (.classMem (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synCpw1 (synChwcn A))))
      (synWb (.classEq
          (synCfv (synChnqmap1 A) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
        (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))))
      p0396 p0397
  have p0399 :=
    @gMpbid (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0392 p0398
  have p0400 :=
    @gJca (.classMem (.cv u) (synChwcn D))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synCcnv (synChnqmap1 E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
      (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0390 p0399
  have p0401 := @gSnex (synCfv (synChncodetrnfn F) (.cv u))
  have p0402 := @gId (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
  have p0403 :=
    @gBreq2d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn F) (.cv u)))) (.cv x)
      (synCsn (synCfv (synChncodetrnfn F) (.cv u)))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
      (synCcnv (synChnqmap1 E)) p0402
  have p0405 :=
    @gBreq1d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn F) (.cv u)))) (.cv x)
      (synCsn (synCfv (synChncodetrnfn F) (.cv u)))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)) (synChnqmap1 A)
      p0402
  have p0406 :=
    @gAnbi12d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synCcnv (synChnqmap1 E)) (.cv x))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synCcnv (synChnqmap1 E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
      (synWbr (.cv x) (synChnqmap1 A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0403 p0405
  have p0407 :=
    @gSpcev
      (synWa (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
          (synCcnv (synChnqmap1 E)) (.cv x)) (synWbr (.cv x) (synChnqmap1 A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))))
      (synWa (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
          (synCcnv (synChnqmap1 E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
        (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))))
      x (synCsn (synCfv (synChncodetrnfn F) (.cv u))) dv_cache_0040 dv_cache_0041 p0401
      p0406
  have p0408 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
          (synCcnv (synChnqmap1 E)) (synCsn (synCfv (synChncodetrnfn F) (.cv u))))
        (synWbr (synCsn (synCfv (synChncodetrnfn F) (.cv u))) (synChnqmap1 A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))))
      (synWex x (synWa
          (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
            (synCcnv (synChnqmap1 E)) (.cv x)) (synWbr (.cv x) (synChnqmap1 A)
            (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))))
      p0400 p0407
  have p0409 :=
    @gBrco x (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)) (synChnqmap1 A)
      (synCcnv (synChnqmap1 E)) dv_cache_0042 dv_cache_0043 dv_cache_0005 dv_cache_0044
  have p0410 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWex x (synWa
          (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
            (synCcnv (synChnqmap1 E)) (.cv x)) (synWbr (.cv x) (synChnqmap1 A)
            (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 E)))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0408 p0409
  have p0411 := (Nominal.classEqRefl (synChnqinc E A))
  have p0412 :=
    @gBreqi (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)) (synChnqinc E A)
      (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 E))) p0411
  have p0413 :=
    @gSylibr (.classMem (.cv u) (synChwcn D))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synCcom (synChnqmap1 A) (synCcnv (synChnqmap1 E)))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synChnqinc E A) (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0410 p0412
  have p0414 := @gHwnisoclasselhnordcl E (synCfv (synChncodetrnfn F) (.cv u)) p0379
  have p0415 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))
      (.classMem (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synChnord E))
      p0300 p0414
  have p0416 := @gHnqincfn A E hyp_hnqinctrnvaldndv_4 p0379 hyp_hnqinctrnvaldndv_5
  have p0417 :=
    @gJctil (.classMem (.cv u) (synChwcn D))
      (.classMem (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synChnord E))
      (synWfn (synChnqinc E A) (synChnord E)) p0415 p0416
  have p0418 :=
    @gFnbrfvb (synChnord E)
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)) (synChnqinc E A)
  have p0419 :=
    @gSyl (.classMem (.cv u) (synChwcn D))
      (synWa (synWfn (synChnqinc E A) (synChnord E))
        (.classMem (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
          (synChnord E)))
      (synWb (.classEq (synCfv (synChnqinc E A)
            (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
        (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
          (synChnqinc E A) (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))))
      p0417 p0418
  have p0420 :=
    @gMpbird (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqinc E A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      (synWbr (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synChnqinc E A) (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A)))
      p0413 p0419
  have p0421 :=
    @gEqtr4d (.classMem (.cv u) (synChwcn D))
      (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D)))
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso A))
      (synCfv (synChnqinc E A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      p0373 p0420
  exact p0421


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part055`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnqinctrnrnssndv`. -/
@[expose]
noncomputable def gHnqinctrnrnssndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hnqinctrnrnssndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hnqinctrnrnssndv_2 : Nominal.NPrf (synWf1o F D E))
    (hyp_hnqinctrnrnssndv_3 : Nominal.NPrf (synWss D A))
    (hyp_hnqinctrnrnssndv_4 : Nominal.NPrf (synWss E A))
    (hyp_hnqinctrnrnssndv_5 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWss (synCrn (synChnqinc D A)) (synCrn (synChnqinc E A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ E.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : x ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synChnqinc D A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0004 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0005 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0006 : u ∉ ((Wff.classMem (.cv y) (synCrn (synChnqinc E A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_y, fresh_u_not_A, fresh_u_not_E, or_false,
          not_false_eq_true])
  have dv_cache_0007 : u ∉ ((synWbr (.cv x) (synChnqinc D A) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_A, fresh_u_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (.cv y) (synCrn (synChnqinc E A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_A, fresh_x_not_E, or_false,
          not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synCrn (synChnqinc D A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_D, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCrn (synChnqinc E A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_E, or_false, not_false_eq_true])
  have p0000 := @gElrn x (.cv y) (synChnqinc D A) dv_cache_0001 dv_cache_0002
  have p0001 := @gBreldm (.cv x) (.cv y) (synChnqinc D A)
  have p0002 := @gF1odm D E F
  have p0003 := Nominal.mp hyp_hnqinctrnrnssndv_2 p0002
  have p0004 := @gDmex F hyp_hnqinctrnrnssndv_1
  have p0005 := @gEqeltrri (synCdm F) D (synCvv) p0003 p0004
  have p0006 := @gHnqincdm A D hyp_hnqinctrnrnssndv_3 p0005 hyp_hnqinctrnrnssndv_5
  have p0007 := @gEleq2i (synCdm (synChnqinc D A)) (synChnord D) (.cv x) p0006
  have p0008 :=
    @gSylib (synWbr (.cv x) (synChnqinc D A) (.cv y))
      (.classMem (.cv x) (synCdm (synChnqinc D A))) (.classMem (.cv x) (synChnord D))
      p0001 p0007
  have p0009 := @gVex x
  have p0010 := @gElhnord x u D dv_cache_0003 dv_cache_0004 dv_cache_0005 p0009
  have p0011 :=
    @gId (synWrex u (synChwcn D) (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
  have p0012 :=
    @gSylbi (.classMem (.cv x) (synChnord D))
      (synWrex u (synChwcn D) (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
      (synWrex u (synChwcn D) (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
      p0010 p0011
  have p0013 :=
    @gSyl (synWbr (.cv x) (synChnqinc D A) (.cv y)) (.classMem (.cv x) (synChnord D))
      (synWrex u (synChwcn D) (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
      p0008 p0012
  have p0014 :=
    @gSimpr (synWbr (.cv x) (synChnqinc D A) (.cv y))
      (synWa (.classMem (.cv u) (synChwcn D))
        (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
  have p0015 :=
    @gSimpr (.classMem (.cv u) (synChwcn D))
      (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))
  have p0016 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synWa (.classMem (.cv u) (synChwcn D))
        (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
      (.classEq (.cv x) (synCec (.cv u) (synChwniso D))) p0014 p0015
  have p0017 :=
    @gFveq2d
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (.cv x) (synCec (.cv u) (synChwniso D)) (synChnqinc D A) p0016
  have p0018 :=
    @gSimpl (synWbr (.cv x) (synChnqinc D A) (.cv y))
      (synWa (.classMem (.cv u) (synChwcn D))
        (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
  have p0023 := @gHnqincfn A D hyp_hnqinctrnrnssndv_3 p0005 hyp_hnqinctrnrnssndv_5
  have p0024 := @gFnfun (synChnord D) (synChnqinc D A)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gFunbrfv (.cv x) (.cv y) (synChnqinc D A)
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synWbr (.cv x) (synChnqinc D A) (.cv y))
      (.classEq (synCfv (synChnqinc D A) (.cv x)) (.cv y)) p0018 p0027
  have p0029 :=
    @gEqtr3d
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synCfv (synChnqinc D A) (.cv x))
      (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D))) (.cv y) p0017 p0028
  have p0031 :=
    @gSimpl (.classMem (.cv u) (synChwcn D))
      (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))
  have p0032 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synWa (.classMem (.cv u) (synChwcn D))
        (.classEq (.cv x) (synCec (.cv u) (synChwniso D))))
      (.classMem (.cv u) (synChwcn D)) p0014 p0031
  have p0033 :=
    @gHnqinctrnvaldndv u A D E F hyp_hnqinctrnrnssndv_1 hyp_hnqinctrnrnssndv_2
      hyp_hnqinctrnrnssndv_3 hyp_hnqinctrnrnssndv_4 hyp_hnqinctrnrnssndv_5
  have p0034 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (.classMem (.cv u) (synChwcn D))
      (.classEq (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D)))
        (synCfv (synChnqinc E A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))))
      p0032 p0033
  have p0035 :=
    @gEqtr3d
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synCfv (synChnqinc D A) (synCec (.cv u) (synChwniso D))) (.cv y)
      (synCfv (synChnqinc E A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      p0029 p0034
  have p0036 := @gF1ofo D E F
  have p0037 := Nominal.mp hyp_hnqinctrnrnssndv_2 p0036
  have p0038 := @gForn D E F
  have p0039 := Nominal.mp p0037 p0038
  have p0040 := @gRnex F hyp_hnqinctrnrnssndv_1
  have p0041 := @gEqeltrri (synCrn F) E (synCvv) p0039 p0040
  have p0042 := @gHnqincfn A E hyp_hnqinctrnrnssndv_4 p0041 hyp_hnqinctrnrnssndv_5
  have p0043 :=
    @gA1i (synWfn (synChnqinc E A) (synChnord E))
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      p0042
  have p0047 := @gHncodetrncndndv u D E F hyp_hnqinctrnrnssndv_1 hyp_hnqinctrnrnssndv_2
  have p0048 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (.classMem (.cv u) (synChwcn D))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E)) p0032 p0047
  have p0055 := @gHwnisoclasselhnordcl E (synCfv (synChncodetrnfn F) (.cv u)) p0041
  have p0056 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (.classMem (synCfv (synChncodetrnfn F) (.cv u)) (synChwcn E))
      (.classMem (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synChnord E))
      p0048 p0055
  have p0057 :=
    @gJca
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synWfn (synChnqinc E A) (synChnord E))
      (.classMem (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
        (synChnord E))
      p0043 p0056
  have p0058 :=
    @gFnfvelrn (synChnord E)
      (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)) (synChnqinc E A)
  have p0059 :=
    @gSyl
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (synWa (synWfn (synChnqinc E A) (synChnord E))
        (.classMem (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E))
          (synChnord E)))
      (.classMem (synCfv (synChnqinc E A)
          (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
        (synCrn (synChnqinc E A)))
      p0057 p0058
  have p0060 :=
    @gEqeltrd
      (synWa (synWbr (.cv x) (synChnqinc D A) (.cv y))
        (synWa (.classMem (.cv u) (synChwcn D))
          (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))))
      (.cv y)
      (synCfv (synChnqinc E A)
        (synCec (synCfv (synChncodetrnfn F) (.cv u)) (synChwniso E)))
      (synCrn (synChnqinc E A)) p0035 p0059
  have p0061 :=
    @gRexlimddv (synWbr (.cv x) (synChnqinc D A) (.cv y))
      (.classEq (.cv x) (synCec (.cv u) (synChwniso D)))
      (.classMem (.cv y) (synCrn (synChnqinc E A))) u (synChwcn D) dv_cache_0006
      dv_cache_0007 p0013 p0060
  have p0062 :=
    @gExlimiv (synWbr (.cv x) (synChnqinc D A) (.cv y))
      (.classMem (.cv y) (synCrn (synChnqinc E A))) x dv_cache_0008 p0061
  have p0063 :=
    @gSylbi (.classMem (.cv y) (synCrn (synChnqinc D A)))
      (synWex x (synWbr (.cv x) (synChnqinc D A) (.cv y)))
      (.classMem (.cv y) (synCrn (synChnqinc E A))) p0000 p0062
  have p0064 :=
    @gSsriv y (synCrn (synChnqinc D A)) (synCrn (synChnqinc E A)) dv_cache_0009
      dv_cache_0010 p0063
  exact p0064

/-- Checked nominal proof certificate identified upstream as `g_hnqinctrnrneqndv`. -/
@[expose]
noncomputable def gHnqinctrnrneqndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hnqinctrnrneqndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hnqinctrnrneqndv_2 : Nominal.NPrf (synWf1o F D E))
    (hyp_hnqinctrnrneqndv_3 : Nominal.NPrf (synWss D A))
    (hyp_hnqinctrnrneqndv_4 : Nominal.NPrf (synWss E A))
    (hyp_hnqinctrnrneqndv_5 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCrn (synChnqinc D A)) (synCrn (synChnqinc E A))) :=
  by
  have p0000 :=
    @gHnqinctrnrnssndv A D E F hyp_hnqinctrnrneqndv_1 hyp_hnqinctrnrneqndv_2
      hyp_hnqinctrnrneqndv_3 hyp_hnqinctrnrneqndv_4 hyp_hnqinctrnrneqndv_5
  have p0001 := @gCnvex F hyp_hnqinctrnrneqndv_1
  have p0002 := @gF1ocnv D E F
  have p0003 := Nominal.mp hyp_hnqinctrnrneqndv_2 p0002
  have p0004 :=
    @gHnqinctrnrnssndv A E D (synCcnv F) p0001 p0003 hyp_hnqinctrnrneqndv_4
      hyp_hnqinctrnrneqndv_3 hyp_hnqinctrnrneqndv_5
  have p0005 :=
    @gEqssi (synCrn (synChnqinc D A)) (synCrn (synChnqinc E A)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnordf1oenambndv`. -/
@[expose]
noncomputable def gHnordf1oenambndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hnordf1oenambndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hnordf1oenambndv_2 : Nominal.NPrf (synWf1o F D E))
    (hyp_hnordf1oenambndv_3 : Nominal.NPrf (synWss D A))
    (hyp_hnordf1oenambndv_4 : Nominal.NPrf (synWss E A))
    (hyp_hnordf1oenambndv_5 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWbr (synChnord D) (synCen) (synChnord E)) :=
  by
  have p0000 := @gF1odm D E F
  have p0001 := Nominal.mp hyp_hnordf1oenambndv_2 p0000
  have p0002 := @gDmex F hyp_hnordf1oenambndv_1
  have p0003 := @gEqeltrri (synCdm F) D (synCvv) p0001 p0002
  have p0004 := @gHnqincf1 A D hyp_hnordf1oenambndv_3 p0003 hyp_hnordf1oenambndv_5
  have p0005 := @gF1f1orn (synChnord D) (synChnord A) (synChnqinc D A)
  have p0006 := Nominal.mp p0004 p0005
  have p0011 :=
    @gPm32i (.classMem D (synCvv)) (.classMem A (synCvv)) p0003 hyp_hnordf1oenambndv_5
  have p0012 := @gHnqincexg A D
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gF1oen (synChnord D) (synCrn (synChnqinc D A)) (synChnqinc D A) p0013
  have p0015 := Nominal.mp p0006 p0014
  have p0016 := @gF1ofo D E F
  have p0017 := Nominal.mp hyp_hnordf1oenambndv_2 p0016
  have p0018 := @gForn D E F
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @gRnex F hyp_hnordf1oenambndv_1
  have p0021 := @gEqeltrri (synCrn F) E (synCvv) p0019 p0020
  have p0022 := @gHnqincf1 A E hyp_hnordf1oenambndv_4 p0021 hyp_hnordf1oenambndv_5
  have p0023 := @gF1f1orn (synChnord E) (synChnord A) (synChnqinc E A)
  have p0024 := Nominal.mp p0022 p0023
  have p0031 :=
    @gPm32i (.classMem E (synCvv)) (.classMem A (synCvv)) p0021 hyp_hnordf1oenambndv_5
  have p0032 := @gHnqincexg A E
  have p0033 := Nominal.mp p0031 p0032
  have p0034 :=
    @gF1oen (synChnord E) (synCrn (synChnqinc E A)) (synChnqinc E A) p0033
  have p0035 := Nominal.mp p0024 p0034
  have p0036 := @gEnsymi (synChnord E) (synCrn (synChnqinc E A))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @gHnqinctrnrneqndv A D E F hyp_hnordf1oenambndv_1 hyp_hnordf1oenambndv_2
      hyp_hnordf1oenambndv_3 hyp_hnordf1oenambndv_4 hyp_hnordf1oenambndv_5
  have p0039 :=
    @gBreq1i (synCrn (synChnqinc D A)) (synCrn (synChnqinc E A)) (synChnord E)
      (synCen) p0038
  have p0040 :=
    @gMpbir (synWbr (synCrn (synChnqinc D A)) (synCen) (synChnord E))
      (synWbr (synCrn (synChnqinc E A)) (synCen) (synChnord E)) p0037 p0039
  have p0041 :=
    @gPm32i (synWbr (synChnord D) (synCen) (synCrn (synChnqinc D A)))
      (synWbr (synCrn (synChnqinc D A)) (synCen) (synChnord E)) p0015 p0040
  have p0042 := @gEntr (synChnord D) (synCrn (synChnqinc D A)) (synChnord E)
  have p0043 := Nominal.mp p0041 p0042
  exact p0043

/-- Checked nominal proof certificate identified upstream as `g_hncardf1oeqambndv`. -/
@[expose]
noncomputable def gHncardf1oeqambndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hncardf1oeqambndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hncardf1oeqambndv_2 : Nominal.NPrf (synWf1o F D E))
    (hyp_hncardf1oeqambndv_3 : Nominal.NPrf (synWss D A))
    (hyp_hncardf1oeqambndv_4 : Nominal.NPrf (synWss E A))
    (hyp_hncardf1oeqambndv_5 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synChncard D) (synChncard E)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncard D))
  have p0001 :=
    @gHnordf1oenambndv A D E F hyp_hncardf1oeqambndv_1 hyp_hncardf1oeqambndv_2
      hyp_hncardf1oeqambndv_3 hyp_hncardf1oeqambndv_4 hyp_hncardf1oeqambndv_5
  have p0002 := @gF1odm D E F
  have p0003 := Nominal.mp hyp_hncardf1oeqambndv_2 p0002
  have p0004 := @gDmex F hyp_hncardf1oeqambndv_1
  have p0005 := @gEqeltrri (synCdm F) D (synCvv) p0003 p0004
  have p0006 := @gHnordexg D
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gEqnc (synChnord D) (synChnord E) p0007
  have p0009 :=
    @gMpbir (.classEq (synCnc (synChnord D)) (synCnc (synChnord E)))
      (synWbr (synChnord D) (synCen) (synChnord E)) p0001 p0008
  have p0010 :=
    @gEqtri (synChncard D) (synCnc (synChnord D)) (synCnc (synChnord E)) p0000 p0009
  have p0011 := (Nominal.classEqRefl (synChncard E))
  have p0012 :=
    @gEqtr4i (synChncard D) (synCnc (synChnord E)) (synChncard E) p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_hncardf1oeqndv`. -/
@[expose]
noncomputable def gHncardf1oeqndv (D : Class) (E : Class) (F : Class)
    (hyp_hncardf1oeqndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_hncardf1oeqndv_2 : Nominal.NPrf (synWf1o F D E)) :
    Nominal.NPrf (.classEq (synChncard D) (synChncard E)) :=
  by
  have p0000 := @gSsun1 D E
  have p0001 := @gSsun2 E D
  have p0002 := @gF1odm D E F
  have p0003 := Nominal.mp hyp_hncardf1oeqndv_2 p0002
  have p0004 := @gDmex F hyp_hncardf1oeqndv_1
  have p0005 := @gEqeltrri (synCdm F) D (synCvv) p0003 p0004
  have p0006 := @gF1ofo D E F
  have p0007 := Nominal.mp hyp_hncardf1oeqndv_2 p0006
  have p0008 := @gForn D E F
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gRnex F hyp_hncardf1oeqndv_1
  have p0011 := @gEqeltrri (synCrn F) E (synCvv) p0009 p0010
  have p0012 := @gUnex D E p0005 p0011
  have p0013 :=
    @gHncardf1oeqambndv (synCun D E) D E F hyp_hncardf1oeqndv_1 hyp_hncardf1oeqndv_2
      p0000 p0001 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_hnordeqdndv`. -/
@[expose]
noncomputable def gHnordeqdndv (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synChnord A) (synChnord B))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnord A))
  have p0001 :=
    @gA1i (.classEq (synChnord A) (synCqs (synChwcn A) (synChwniso A)))
      (.classEq A B) p0000
  have p0002 := (Nominal.classEqRefl (synChwcn A))
  have p0003 :=
    @gA1i (.classEq (synChwcn A) (synCin (synChwcodes A) (synChwrels)))
      (.classEq A B) p0002
  have p0004 := (Nominal.classEqRefl (synChwcodes A))
  have p0005 :=
    @gA1i (.classEq (synChwcodes A) (synCin (synCwe) (synCxp (synCvv) (synCpw A))))
      (.classEq A B) p0004
  have p0006 := @gPweq A B
  have p0007 := @gXpeq2d (.classEq A B) (synCpw A) (synCpw B) (synCvv) p0006
  have p0008 :=
    @gIneq2d (.classEq A B) (synCxp (synCvv) (synCpw A))
      (synCxp (synCvv) (synCpw B)) (synCwe) p0007
  have p0009 :=
    @gEqtrd (.classEq A B) (synChwcodes A)
      (synCin (synCwe) (synCxp (synCvv) (synCpw A)))
      (synCin (synCwe) (synCxp (synCvv) (synCpw B))) p0005 p0008
  have p0010 := (Nominal.classEqRefl (synChwcodes B))
  have p0011 :=
    @gEqcomi (synChwcodes B) (synCin (synCwe) (synCxp (synCvv) (synCpw B))) p0010
  have p0012 :=
    @gA1i (.classEq (synCin (synCwe) (synCxp (synCvv) (synCpw B))) (synChwcodes B))
      (.classEq A B) p0011
  have p0013 :=
    @gEqtrd (.classEq A B) (synChwcodes A)
      (synCin (synCwe) (synCxp (synCvv) (synCpw B))) (synChwcodes B) p0009 p0012
  have p0014 :=
    @gIneq1d (.classEq A B) (synChwcodes A) (synChwcodes B) (synChwrels) p0013
  have p0015 :=
    @gEqtrd (.classEq A B) (synChwcn A) (synCin (synChwcodes A) (synChwrels))
      (synCin (synChwcodes B) (synChwrels)) p0003 p0014
  have p0016 := (Nominal.classEqRefl (synChwcn B))
  have p0017 := @gEqcomi (synChwcn B) (synCin (synChwcodes B) (synChwrels)) p0016
  have p0018 :=
    @gA1i (.classEq (synCin (synChwcodes B) (synChwrels)) (synChwcn B))
      (.classEq A B) p0017
  have p0019 :=
    @gEqtrd (.classEq A B) (synChwcn A) (synCin (synChwcodes B) (synChwrels))
      (synChwcn B) p0015 p0018
  have p0020 := @gQseq1 (synChwcn A) (synChwcn B) (synChwniso A)
  have p0021 :=
    @gSyl (.classEq A B) (.classEq (synChwcn A) (synChwcn B))
      (.classEq (synCqs (synChwcn A) (synChwniso A)) (synCqs (synChwcn B) (synChwniso A)))
      p0019 p0020
  have p0022 := (Nominal.classEqRefl (synChwniso A))
  have p0023 :=
    @gA1i
      (.classEq (synChwniso A)
        (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn A) (synChwcn A))))
      (.classEq A B) p0022
  have p0060 :=
    @gXpeq12d (.classEq A B) (synChwcn A) (synChwcn B) (synChwcn A) (synChwcn B)
      p0019 p0019
  have p0061 :=
    @gIneq2d (.classEq A B) (synCxp (synChwcn A) (synChwcn A))
      (synCxp (synChwcn B) (synChwcn B))
      (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) p0060
  have p0062 :=
    @gEqtrd (.classEq A B) (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn B) (synChwcn B)))
      p0023 p0061
  have p0063 := (Nominal.classEqRefl (synChwniso B))
  have p0064 :=
    @gEqcomi (synChwniso B)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn B) (synChwcn B)))
      p0063
  have p0065 :=
    @gA1i
      (.classEq (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn B) (synChwcn B))) (synChwniso B))
      (.classEq A B) p0064
  have p0066 :=
    @gEqtrd (.classEq A B) (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn B) (synChwcn B)))
      (synChwniso B) p0062 p0065
  have p0067 := @gQseq2 (synChwniso A) (synChwniso B) (synChwcn B)
  have p0068 :=
    @gSyl (.classEq A B) (.classEq (synChwniso A) (synChwniso B))
      (.classEq (synCqs (synChwcn B) (synChwniso A)) (synCqs (synChwcn B) (synChwniso B)))
      p0066 p0067
  have p0069 :=
    @gEqtrd (.classEq A B) (synCqs (synChwcn A) (synChwniso A))
      (synCqs (synChwcn B) (synChwniso A)) (synCqs (synChwcn B) (synChwniso B))
      p0021 p0068
  have p0070 :=
    @gEqtrd (.classEq A B) (synChnord A) (synCqs (synChwcn A) (synChwniso A))
      (synCqs (synChwcn B) (synChwniso B)) p0001 p0069
  have p0071 := (Nominal.classEqRefl (synChnord B))
  have p0072 := @gEqcomi (synChnord B) (synCqs (synChwcn B) (synChwniso B)) p0071
  have p0073 :=
    @gA1i (.classEq (synCqs (synChwcn B) (synChwniso B)) (synChnord B))
      (.classEq A B) p0072
  have p0074 :=
    @gEqtrd (.classEq A B) (synChnord A) (synCqs (synChwcn B) (synChwniso B))
      (synChnord B) p0070 p0073
  exact p0074

/-- Checked nominal proof certificate identified upstream as `g_hncardeqdndv`. -/
@[expose]
noncomputable def gHncardeqdndv (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synChncard A) (synChncard B))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncard A))
  have p0001 :=
    @gA1i (.classEq (synChncard A) (synCnc (synChnord A))) (.classEq A B) p0000
  have p0002 := (Nominal.classEqRefl (synChnord A))
  have p0003 :=
    @gA1i (.classEq (synChnord A) (synCqs (synChwcn A) (synChwniso A)))
      (.classEq A B) p0002
  have p0004 := (Nominal.classEqRefl (synChwcn A))
  have p0005 :=
    @gA1i (.classEq (synChwcn A) (synCin (synChwcodes A) (synChwrels)))
      (.classEq A B) p0004
  have p0006 := (Nominal.classEqRefl (synChwcodes A))
  have p0007 :=
    @gA1i (.classEq (synChwcodes A) (synCin (synCwe) (synCxp (synCvv) (synCpw A))))
      (.classEq A B) p0006
  have p0008 := @gPweq A B
  have p0009 := @gXpeq2d (.classEq A B) (synCpw A) (synCpw B) (synCvv) p0008
  have p0010 :=
    @gIneq2d (.classEq A B) (synCxp (synCvv) (synCpw A))
      (synCxp (synCvv) (synCpw B)) (synCwe) p0009
  have p0011 :=
    @gEqtrd (.classEq A B) (synChwcodes A)
      (synCin (synCwe) (synCxp (synCvv) (synCpw A)))
      (synCin (synCwe) (synCxp (synCvv) (synCpw B))) p0007 p0010
  have p0012 := (Nominal.classEqRefl (synChwcodes B))
  have p0013 :=
    @gEqcomi (synChwcodes B) (synCin (synCwe) (synCxp (synCvv) (synCpw B))) p0012
  have p0014 :=
    @gA1i (.classEq (synCin (synCwe) (synCxp (synCvv) (synCpw B))) (synChwcodes B))
      (.classEq A B) p0013
  have p0015 :=
    @gEqtrd (.classEq A B) (synChwcodes A)
      (synCin (synCwe) (synCxp (synCvv) (synCpw B))) (synChwcodes B) p0011 p0014
  have p0016 :=
    @gIneq1d (.classEq A B) (synChwcodes A) (synChwcodes B) (synChwrels) p0015
  have p0017 :=
    @gEqtrd (.classEq A B) (synChwcn A) (synCin (synChwcodes A) (synChwrels))
      (synCin (synChwcodes B) (synChwrels)) p0005 p0016
  have p0018 := (Nominal.classEqRefl (synChwcn B))
  have p0019 := @gEqcomi (synChwcn B) (synCin (synChwcodes B) (synChwrels)) p0018
  have p0020 :=
    @gA1i (.classEq (synCin (synChwcodes B) (synChwrels)) (synChwcn B))
      (.classEq A B) p0019
  have p0021 :=
    @gEqtrd (.classEq A B) (synChwcn A) (synCin (synChwcodes B) (synChwrels))
      (synChwcn B) p0017 p0020
  have p0022 := @gQseq1 (synChwcn A) (synChwcn B) (synChwniso A)
  have p0023 :=
    @gSyl (.classEq A B) (.classEq (synChwcn A) (synChwcn B))
      (.classEq (synCqs (synChwcn A) (synChwniso A)) (synCqs (synChwcn B) (synChwniso A)))
      p0021 p0022
  have p0024 := (Nominal.classEqRefl (synChwniso A))
  have p0025 :=
    @gA1i
      (.classEq (synChwniso A)
        (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn A) (synChwcn A))))
      (.classEq A B) p0024
  have p0062 :=
    @gXpeq12d (.classEq A B) (synChwcn A) (synChwcn B) (synChwcn A) (synChwcn B)
      p0021 p0021
  have p0063 :=
    @gIneq2d (.classEq A B) (synCxp (synChwcn A) (synChwcn A))
      (synCxp (synChwcn B) (synChwcn B))
      (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) p0062
  have p0064 :=
    @gEqtrd (.classEq A B) (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn B) (synChwcn B)))
      p0025 p0063
  have p0065 := (Nominal.classEqRefl (synChwniso B))
  have p0066 :=
    @gEqcomi (synChwniso B)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn B) (synChwcn B)))
      p0065
  have p0067 :=
    @gA1i
      (.classEq (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn B) (synChwcn B))) (synChwniso B))
      (.classEq A B) p0066
  have p0068 :=
    @gEqtrd (.classEq A B) (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn B) (synChwcn B)))
      (synChwniso B) p0064 p0067
  have p0069 := @gQseq2 (synChwniso A) (synChwniso B) (synChwcn B)
  have p0070 :=
    @gSyl (.classEq A B) (.classEq (synChwniso A) (synChwniso B))
      (.classEq (synCqs (synChwcn B) (synChwniso A)) (synCqs (synChwcn B) (synChwniso B)))
      p0068 p0069
  have p0071 :=
    @gEqtrd (.classEq A B) (synCqs (synChwcn A) (synChwniso A))
      (synCqs (synChwcn B) (synChwniso A)) (synCqs (synChwcn B) (synChwniso B))
      p0023 p0070
  have p0072 :=
    @gEqtrd (.classEq A B) (synChnord A) (synCqs (synChwcn A) (synChwniso A))
      (synCqs (synChwcn B) (synChwniso B)) p0003 p0071
  have p0073 := (Nominal.classEqRefl (synChnord B))
  have p0074 := @gEqcomi (synChnord B) (synCqs (synChwcn B) (synChwniso B)) p0073
  have p0075 :=
    @gA1i (.classEq (synCqs (synChwcn B) (synChwniso B)) (synChnord B))
      (.classEq A B) p0074
  have p0076 :=
    @gEqtrd (.classEq A B) (synChnord A) (synCqs (synChwcn B) (synChwniso B))
      (synChnord B) p0072 p0075
  have p0077 := @gNceqd (.classEq A B) (synChnord A) (synChnord B) p0076
  have p0078 :=
    @gEqtrd (.classEq A B) (synChncard A) (synCnc (synChnord A))
      (synCnc (synChnord B)) p0001 p0077
  have p0079 := (Nominal.classEqRefl (synChncard B))
  have p0080 := @gEqcomi (synChncard B) (synCnc (synChnord B)) p0079
  have p0081 :=
    @gA1i (.classEq (synCnc (synChnord B)) (synChncard B)) (.classEq A B) p0080
  have p0082 :=
    @gEqtrd (.classEq A B) (synChncard A) (synCnc (synChnord B)) (synChncard B) p0078
      p0081
  exact p0082

/-- Checked nominal proof certificate identified upstream as `g_hncardf1oimpndv`. -/
@[expose]
noncomputable def gHncardf1oimpndv (D : Class) (E : Class) (F : Class)
    (hyp_hncardf1oimpndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.imp (synWf1o F D E) (.classEq (synChncard D) (synChncard E))) :=
  by
  have p0000 := @gIftrue (synWf1o F D E) D (synC0)
  have p0001 := @gHncardeqdndv (synCif (synWf1o F D E) D (synC0)) D
  have p0002 :=
    @gSyl (synWf1o F D E) (.classEq (synCif (synWf1o F D E) D (synC0)) D)
      (.classEq (synChncard (synCif (synWf1o F D E) D (synC0))) (synChncard D)) p0000
      p0001
  have p0003 :=
    @gEqcomd (synWf1o F D E) (synChncard (synCif (synWf1o F D E) D (synC0)))
      (synChncard D) p0002
  have p0004 := @gN0ex
  have p0005 := @gIfex (synWf1o F D E) F (synC0) hyp_hncardf1oimpndv_1 p0004
  have p0006 := @gId (synWf1o F D E)
  have p0007 := @gIftrue (synWf1o F D E) F (synC0)
  have p0008 :=
    @gF1oeq1 (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0))
      (synCif (synWf1o F D E) F (synC0)) F
  have p0009 :=
    @gSyl (synWf1o F D E) (.classEq (synCif (synWf1o F D E) F (synC0)) F)
      (synWb (synWf1o (synCif (synWf1o F D E) F (synC0))
          (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
        (synWf1o F (synCif (synWf1o F D E) D (synC0))
          (synCif (synWf1o F D E) E (synC0))))
      p0007 p0008
  have p0011 :=
    @gF1oeq2 (synCif (synWf1o F D E) D (synC0)) D
      (synCif (synWf1o F D E) E (synC0)) F
  have p0012 :=
    @gSyl (synWf1o F D E) (.classEq (synCif (synWf1o F D E) D (synC0)) D)
      (synWb (synWf1o F (synCif (synWf1o F D E) D (synC0))
          (synCif (synWf1o F D E) E (synC0)))
        (synWf1o F D (synCif (synWf1o F D E) E (synC0))))
      p0000 p0011
  have p0013 :=
    @gBitrd (synWf1o F D E)
      (synWf1o (synCif (synWf1o F D E) F (synC0))
        (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
      (synWf1o F (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
      (synWf1o F D (synCif (synWf1o F D E) E (synC0))) p0009 p0012
  have p0014 := @gIftrue (synWf1o F D E) E (synC0)
  have p0015 := @gF1oeq3 (synCif (synWf1o F D E) E (synC0)) E D F
  have p0016 :=
    @gSyl (synWf1o F D E) (.classEq (synCif (synWf1o F D E) E (synC0)) E)
      (synWb (synWf1o F D (synCif (synWf1o F D E) E (synC0))) (synWf1o F D E)) p0014
      p0015
  have p0017 :=
    @gBitrd (synWf1o F D E)
      (synWf1o (synCif (synWf1o F D E) F (synC0))
        (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
      (synWf1o F D (synCif (synWf1o F D E) E (synC0))) (synWf1o F D E) p0013 p0016
  have p0018 :=
    @gMpbird (synWf1o F D E)
      (synWf1o (synCif (synWf1o F D E) F (synC0))
        (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
      (synWf1o F D E) p0006 p0017
  have p0019 := @gF1o0
  have p0020 := @gIffalse (synWf1o F D E) F (synC0)
  have p0021 := @gF1oeq1 (synC0) (synC0) (synCif (synWf1o F D E) F (synC0)) (synC0)
  have p0022 :=
    @gSyl (.neg (synWf1o F D E))
      (.classEq (synCif (synWf1o F D E) F (synC0)) (synC0))
      (synWb (synWf1o (synCif (synWf1o F D E) F (synC0)) (synC0) (synC0))
        (synWf1o (synC0) (synC0) (synC0)))
      p0020 p0021
  have p0023 :=
    @gMpbiri (.neg (synWf1o F D E))
      (synWf1o (synCif (synWf1o F D E) F (synC0)) (synC0) (synC0))
      (synWf1o (synC0) (synC0) (synC0)) p0019 p0022
  have p0024 := @gIffalse (synWf1o F D E) D (synC0)
  have p0025 := @gIffalse (synWf1o F D E) E (synC0)
  have p0026 :=
    @gJca (.neg (synWf1o F D E))
      (.classEq (synCif (synWf1o F D E) D (synC0)) (synC0))
      (.classEq (synCif (synWf1o F D E) E (synC0)) (synC0)) p0024 p0025
  have p0027 :=
    @gF1oeq23 (synCif (synWf1o F D E) D (synC0)) (synC0)
      (synCif (synWf1o F D E) E (synC0)) (synC0) (synCif (synWf1o F D E) F (synC0))
  have p0028 :=
    @gSyl (.neg (synWf1o F D E))
      (synWa (.classEq (synCif (synWf1o F D E) D (synC0)) (synC0))
        (.classEq (synCif (synWf1o F D E) E (synC0)) (synC0)))
      (synWb (synWf1o (synCif (synWf1o F D E) F (synC0))
          (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
        (synWf1o (synCif (synWf1o F D E) F (synC0)) (synC0) (synC0)))
      p0026 p0027
  have p0029 :=
    @gMpbird (.neg (synWf1o F D E))
      (synWf1o (synCif (synWf1o F D E) F (synC0))
        (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
      (synWf1o (synCif (synWf1o F D E) F (synC0)) (synC0) (synC0)) p0023 p0028
  have p0030 :=
    @gPm261i (synWf1o F D E)
      (synWf1o (synCif (synWf1o F D E) F (synC0))
        (synCif (synWf1o F D E) D (synC0)) (synCif (synWf1o F D E) E (synC0)))
      p0018 p0029
  have p0031 :=
    @gHncardf1oeqndv (synCif (synWf1o F D E) D (synC0))
      (synCif (synWf1o F D E) E (synC0)) (synCif (synWf1o F D E) F (synC0)) p0005
      p0030
  have p0032 :=
    @gA1i
      (.classEq (synChncard (synCif (synWf1o F D E) D (synC0)))
        (synChncard (synCif (synWf1o F D E) E (synC0))))
      (synWf1o F D E) p0031
  have p0033 :=
    @gEqtrd (synWf1o F D E) (synChncard D)
      (synChncard (synCif (synWf1o F D E) D (synC0)))
      (synChncard (synCif (synWf1o F D E) E (synC0))) p0003 p0032
  have p0035 := @gHncardeqdndv (synCif (synWf1o F D E) E (synC0)) E
  have p0036 :=
    @gSyl (synWf1o F D E) (.classEq (synCif (synWf1o F D E) E (synC0)) E)
      (.classEq (synChncard (synCif (synWf1o F D E) E (synC0))) (synChncard E)) p0014
      p0035
  have p0037 :=
    @gEqtrd (synWf1o F D E) (synChncard D)
      (synChncard (synCif (synWf1o F D E) E (synC0))) (synChncard E) p0033 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_hncardnceqdndv`. -/
@[expose]
noncomputable def gHncardnceqdndv (D : Class) (E : Class)
    (hyp_hncardnceqdndv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (_hyp_hncardnceqdndv_2 : Nominal.NPrf (.classMem E (synCvv))) :
    Nominal.NPrf
      (.imp (.classEq (synCnc D) (synCnc E)) (.classEq (synChncard D) (synChncard E))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_D, not_false_eq_true])
  have dv_cache_0002 : f ∉ (E).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_E, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (synChncard D) (synChncard E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union,
          fresh_f_not_D, fresh_f_not_E, or_false, not_false_eq_true])
  have p0000 := @gEqnc D E hyp_hncardnceqdndv_1
  have p0001 := @gBiimpi (.classEq (synCnc D) (synCnc E)) (synWbr D (synCen) E) p0000
  have p0002 := @gBren D E f dv_cache_0001 dv_cache_0002
  have p0003 := @gBiimpi (synWbr D (synCen) E) (synWex f (synWf1o (.cv f) D E)) p0002
  have p0004 :=
    @gSyl (.classEq (synCnc D) (synCnc E)) (synWbr D (synCen) E)
      (synWex f (synWf1o (.cv f) D E)) p0001 p0003
  have p0005 := @gVex f
  have p0006 := @gHncardf1oimpndv D E (.cv f) p0005
  have p0007 :=
    @gExlimiv (synWf1o (.cv f) D E) (.classEq (synChncard D) (synChncard E)) f
      dv_cache_0003 p0006
  have p0008 :=
    @gSyl (.classEq (synCnc D) (synCnc E)) (synWex f (synWf1o (.cv f) D E))
      (.classEq (synChncard D) (synChncard E)) p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hncardnceqndv`. -/
@[expose]
noncomputable def gHncardnceqndv (D : Class) (E : Class)
    (hyp_hncardnceqndv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hncardnceqndv_2 : Nominal.NPrf (.classMem E (synCvv)))
    (hyp_hncardnceqndv_3 : Nominal.NPrf (.classEq (synCnc D) (synCnc E))) :
    Nominal.NPrf (.classEq (synChncard D) (synChncard E)) :=
  by
  have p0000 := @gHncardnceqdndv D E hyp_hncardnceqndv_1 hyp_hncardnceqndv_2
  have p0001 := Nominal.mp hyp_hncardnceqndv_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wppcardt4fnexndv`. -/
@[expose]
noncomputable def gWppcardt4fnexndv :
    Nominal.NPrf (.classMem (synCwppcardt4fn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardt4fn))
  have p0001 := @gWppcardt2fnexndv
  have p0003 := @gSiex (synCwppcardt2fn) p0001
  have p0004 := @gSiex (synCsi (synCwppcardt2fn)) p0003
  have p0005 :=
    @gCoex (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))) p0001 p0004
  have p0006 :=
    @gEqeltri (synCwppcardt4fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn)))) (synCvv) p0000
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_wppcardt4fnmapndv`. -/
@[expose]
noncomputable def gWppcardt4fnmapndv :
    Nominal.NPrf
      (synWf (synCwppcardt4fn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
        (synCncs)) :=
  by
  have p0000 := @gWppcardt2fnmapndv
  have p0002 := @gSifmap (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
  have p0003 := Nominal.mp p0000 p0002
  have p0004 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCncs))
      (synCsi (synCwppcardt2fn))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i (synWf (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf (synCsi (synCsi (synCwppcardt2fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCpw1 (synCpw1 (synCncs))))
      p0000 p0005
  have p0007 :=
    @gFco (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt2fn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (synCwppcardt4fn))
  have p0010 :=
    @gFeq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn)))) p0009
  have p0011 :=
    @gMpbir
      (synWf (synCwppcardt4fn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
        (synCncs))
      (synWf (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs))
      p0008 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end
