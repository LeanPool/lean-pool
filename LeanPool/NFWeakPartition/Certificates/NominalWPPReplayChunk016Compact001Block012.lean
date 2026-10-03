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

@[expose]
noncomputable def g_pwpullwesetimpndv (x : Var) (y : Var) (f : Var) (r : Var)
    (_dv_f_r : f ≠ r) (_dv_f_x : f ≠ x) (_dv_f_y : f ≠ y) (_dv_r_x : r ≠ x)
    (_dv_r_y : r ≠ y) (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))) :=
  by
  exact
    (g_pwpullwesetimpndv_stage1 x y f r
      (fun p0000 p0004 p0015 p0018 p0022 p0027 p0036 p0038 p0039 p0042 p0045 p0046 p0047
          p0049 p0050 p0055 p0058 p0059 p0066 p0081 p0082 p0090 p0101 p0102 p0113 p0114
          p0115 p0116 p0117 p0126 p0130 p0132 p0134 p0135 p0137 p0140 p0141 p0162 p0165
          p0169 p0172 p0185 p0190 p0193 p0195 p0201 p0202 p0212 p0277 p0278 p0282 p0283
          p0286 p0289 p0290 p0293 p0294 =>
        (g_pwpullwesetimpndv_stage2 x y f r p0000 p0004 p0018 p0022 p0027 p0036 p0039
          p0045 p0047 p0050 p0055 p0059 p0066 p0082 p0090 p0102 p0115 p0117 p0130 p0132
          p0134 p0135 p0137 p0140 p0141 p0162 p0165 p0169 p0172 p0185 p0190 p0193 p0195
          p0201 p0202 p0212 p0278 p0282 p0283 p0289 p0290 p0293 p0294
          (fun p0318 p0331 p0335 p0437 p0440 p0452 p0517 p0537 p0538 p0556 p0561 p0574 p0581 =>
            (g_pwpullwesetimpndv_stage3 x y f r p0000 p0004 p0022 p0027 p0042 p0046 p0101
              p0113 p0115 p0116 p0117 p0126 p0277 p0318 p0331 p0335 p0437 p0452 p0517
              p0537 p0538 p0556 p0561 p0574 p0581
              (fun p0607 p0615 p0687 p0690 p0693 p0694 p0696 p0709 p0766 p0769 p0770 p0776
                  p0777 p0780 p0782 p0801 p0802 p0807 p0811 p0812 =>
                (g_pwpullwesetimpndv_stage4 x y f r p0015 p0042 p0286 p0615 p0766 p0769
                  p0770 p0776 p0780 p0782 p0801 p0802 p0807 p0811 p0812
                  (fun p0854 p0978 p0984 p0992 p0994 p0995 p0997 p1000 =>
                    (g_pwpullwesetimpndv_stage5 x y f r p0000 p0036 p0038 p0039 p0042
                      p0045 p0047 p0049 p0050 p0055 p0058 p0081 p0101 p0114 p0117 p0162
                      p0169 p0185 p0193 p0201 p0318 p0709 p0854 p0978 p0984 p0992 p0994
                      p0995 p0997 p1000 (fun p1293 p1294 p1299 =>
                        (g_pwpullwesetimpndv_stage6 x y f r p0000 p0115 p0117 p0440 p0607
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

@[expose]
noncomputable def g_pwpullssxpsetimpndv (x : Var) (y : Var) (f : Var) (r : Var)
    (_dv_f_r : f ≠ r) (_dv_f_x : f ≠ x) (_dv_f_y : f ≠ y) (_dv_r_x : r ≠ x)
    (_dv_r_y : r ≠ y) (_dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wfo (.cv f) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))) :=
  by
  have p0000 := @g_ssdmrn (syn_cpwpull (.cv f) (.cv r))
  have p0001 := (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r)))
  have p0002 :=
    @g_dmeqi (syn_cpwpull (.cv f) (.cv r))
      (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0001
  have p0003 := @g_dmcoss (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)
  have p0004 :=
    @g_eqsstri (syn_cdm (syn_cpwpull (.cv f) (.cv r)))
      (syn_cdm (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f))) (syn_cdm (.cv f))
      p0002 p0003
  have p0005 := @g_fofn (.cv x) (.cv y) (.cv f)
  have p0006 := @g_id (syn_wfo (.cv f) (.cv x) (.cv y))
  have p0007 :=
    @g_a1ii (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfn (.cv f) (.cv x)))
      (.imp (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfo (.cv f) (.cv x) (.cv y))) p0005
      p0006
  have p0008 := @g_fndm (.cv x) (.cv f)
  have p0009 :=
    @g_syl (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfn (.cv f) (.cv x))
      (.classEq (syn_cdm (.cv f)) (.cv x)) p0007 p0008
  have p0010 :=
    @g_syl5sseq (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_cdm (.cv f))
      (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x) p0004 p0009
  have p0012 :=
    @g_rneqi (syn_cpwpull (.cv f) (.cv r))
      (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0001
  have p0013 := @g_rncoss (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)
  have p0014 :=
    @g_eqsstri (syn_crn (syn_cpwpull (.cv f) (.cv r)))
      (syn_crn (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)))
      (syn_crn (syn_ccom (syn_ccnv (.cv f)) (.cv r))) p0012 p0013
  have p0015 := @g_rncoss (syn_ccnv (.cv f)) (.cv r)
  have p0016 :=
    @g_sstri (syn_crn (syn_cpwpull (.cv f) (.cv r)))
      (syn_crn (syn_ccom (syn_ccnv (.cv f)) (.cv r))) (syn_crn (syn_ccnv (.cv f))) p0014
      p0015
  have p0017 := @g_dfrn4 (syn_ccnv (.cv f))
  have p0018 := @g_cnvcnv (.cv f)
  have p0019 := @g_dmeqi (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0018
  have p0020 :=
    @g_eqtri (syn_crn (syn_ccnv (.cv f))) (syn_cdm (syn_ccnv (syn_ccnv (.cv f))))
      (syn_cdm (.cv f)) p0017 p0019
  have p0021 :=
    @g_sseqtri (syn_crn (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_ccnv (.cv f)))
      (syn_cdm (.cv f)) p0016 p0020
  have p0022 :=
    @g_syl5sseq (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_cdm (.cv f))
      (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x) p0021 p0009
  have p0023 :=
    @g_jca (syn_wfo (.cv f) (.cv x) (.cv y))
      (syn_wss (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x))
      (syn_wss (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x)) p0010 p0022
  have p0024 :=
    @g_xpss12 (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x)
      (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x)
  have p0025 :=
    @g_syl (syn_wfo (.cv f) (.cv x) (.cv y))
      (syn_wa (syn_wss (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (.cv x))
        (syn_wss (syn_crn (syn_cpwpull (.cv f) (.cv r))) (.cv x)))
      (syn_wss (syn_cxp (syn_cdm (syn_cpwpull (.cv f) (.cv r)))
          (syn_crn (syn_cpwpull (.cv f) (.cv r)))) (syn_cxp (.cv x) (.cv x)))
      p0023 p0024
  have p0026 :=
    @g_syl5ss (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_cpwpull (.cv f) (.cv r))
      (syn_cxp (syn_cdm (syn_cpwpull (.cv f) (.cv r))) (syn_crn (syn_cpwpull (.cv f) (.cv r))))
      (syn_cxp (.cv x) (.cv x)) p0000 p0025
  exact p0026

@[expose]
noncomputable def g_elhwcodesclndv (B : Class) (C : Class) (D : Class)
    (hyp_elhwcodesclndv_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_elhwcodesclndv_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop B C) (syn_chwcodes D))
        (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D))) :=
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
      ((syn_wb (.classMem (syn_cop B C) (syn_chwcodes D))
          (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D)))).fv :=
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
  have p0000 := @g_id (.classEq (.cv r) B)
  have p0001 := @g_opeq1d (.classEq (.cv r) B) (.cv r) B C p0000
  have p0002 :=
    @g_eleq1d (.classEq (.cv r) B) (syn_cop (.cv r) C) (syn_cop B C) (syn_chwcodes D)
      p0001
  have p0004 := @g_breq1d (.classEq (.cv r) B) (.cv r) B C (syn_cwe) p0000
  have p0005 := @g_biid (syn_wss C D)
  have p0006 := @g_a1i (syn_wb (syn_wss C D) (syn_wss C D)) (.classEq (.cv r) B) p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv r) B) (syn_wbr (.cv r) (syn_cwe) C) (syn_wbr B (syn_cwe) C)
      (syn_wss C D) (syn_wss C D) p0004 p0006
  have p0008 :=
    @g_bibi12d (.classEq (.cv r) B) (.classMem (syn_cop (.cv r) C) (syn_chwcodes D))
      (.classMem (syn_cop B C) (syn_chwcodes D))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) C) (syn_wss C D))
      (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D)) p0002 p0007
  have p0009 := @g_vex r
  have p0010 := @g_elhwcodes D C (.cv r) dv_cache_0001 p0009 hyp_elhwcodesclndv_2
  have p0011 :=
    @g_vtocl
      (syn_wb (.classMem (syn_cop (.cv r) C) (syn_chwcodes D))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) C) (syn_wss C D)))
      (syn_wb (.classMem (syn_cop B C) (syn_chwcodes D))
        (syn_wa (syn_wbr B (syn_cwe) C) (syn_wss C D)))
      r B dv_cache_0002 dv_cache_0003 hyp_elhwcodesclndv_1 p0008 p0010
  exact p0011

@[expose]
noncomputable def g_hwbijf1oclndv (B : Class)
    (hyp_hwbijf1oclndv_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem B (syn_chwbij)) (syn_wf1o B (syn_cdm B) (syn_crn B))) :=
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
    f ∉ ((syn_wb (.classMem B (syn_chwbij)) (syn_wf1o B (syn_cdm B) (syn_crn B)))).fv :=
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
  have p0000 := @g_id (.classEq (.cv f) B)
  have p0001 := @g_eleq1d (.classEq (.cv f) B) (.cv f) B (syn_chwbij) p0000
  have p0002 := @g_f1oeq1 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv f) B
  have p0004 := @g_dmeqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0006 := @g_rneqd (.classEq (.cv f) B) (.cv f) B p0000
  have p0007 :=
    @g_jca (.classEq (.cv f) B) (.classEq (syn_cdm (.cv f)) (syn_cdm B))
      (.classEq (syn_crn (.cv f)) (syn_crn B)) p0004 p0006
  have p0008 := @g_f1oeq23 (syn_cdm (.cv f)) (syn_cdm B) (syn_crn (.cv f)) (syn_crn B) B
  have p0009 :=
    @g_syl (.classEq (.cv f) B)
      (syn_wa (.classEq (syn_cdm (.cv f)) (syn_cdm B)) (.classEq (syn_crn (.cv f)) (syn_crn B)))
      (syn_wb (syn_wf1o B (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wf1o B (syn_cdm B) (syn_crn B)))
      p0007 p0008
  have p0010 :=
    @g_bitrd (.classEq (.cv f) B) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o B (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o B (syn_cdm B) (syn_crn B)) p0002 p0009
  have p0011 :=
    @g_bibi12d (.classEq (.cv f) B) (.classMem (.cv f) (syn_chwbij))
      (.classMem B (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o B (syn_cdm B) (syn_crn B)) p0001 p0010
  have p0012 := @g_hwbijf1o f
  have p0013 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv f) (syn_chwbij))
        (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))))
      (syn_wb (.classMem B (syn_chwbij)) (syn_wf1o B (syn_cdm B) (syn_crn B))) f B
      (syn_cvv) dv_cache_0001 dv_cache_0002 p0011 p0012
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

@[expose]
noncomputable def g_hncodetrncndndv (u : Var) (D : Class) (E : Class) (F : Class)
    (hyp_hncodetrncndndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hncodetrncndndv_2 : Nominal.NPrf (syn_wf1o F D E)) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn D))
        (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))) :=
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
  have dv_cache_0007 : f ∉ ((syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
              (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cwe) (.cv x)))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
            (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe)
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
  have dv_cache_0013 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
          (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cxp (.cv x) (.cv x))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
  have p0000 := @g_vex u
  have p0001 := @g_hncodetrnfnvalndv u F hyp_hncodetrncndndv_1 p0000
  have p0002 :=
    (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u))))
  have p0003 := @g_cnvcnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0004 :=
    @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0003
  have p0005 :=
    @g_coeq1i
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0004
  have p0006 :=
    @g_eqtri
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0002 p0005
  have p0007 := @g_hwcnpair u D
  have p0008 := @g_id (.classMem (.cv u) (syn_chwcn D))
  have p0009 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv u)
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0007
      p0008
  have p0011 := @g_elhwcncl D (.cv u)
  have p0012 := Nominal.mp p0000 p0011
  have p0013 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0012
  have p0014 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D))
          (syn_wss (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0013
      p0008
  have p0015 :=
    @g_simpl (.classMem (.cv u) (syn_chwcodes D))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
  have p0016 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcodes D)) p0014 p0015
  have p0017 :=
    @g_eqeltrrd (.classMem (.cv u) (syn_chwcn D)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)
      p0009 p0016
  have p0018 := @g_fvex (.cv u) (syn_c1st)
  have p0019 := @g_fvex (.cv u) (syn_c2nd)
  have p0020 :=
    @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) D p0018
      p0019
  have p0021 :=
    @g_sylib (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      p0017 p0020
  have p0022 :=
    @g_simpr (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0023 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0021 p0022
  have p0024 := @g_f1of1 D E F
  have p0025 := Nominal.mp hyp_hncodetrncndndv_2 p0024
  have p0026 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
      (syn_wf1 F D E) p0023 p0025
  have p0027 := @g_f1ores D E (syn_cfv (syn_c2nd) (.cv u)) F
  have p0028 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wf1 F D E) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      p0026 p0027
  have p0029 :=
    @g_f1odm (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0030 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c2nd) (.cv u)))
      p0028 p0029
  have p0031 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      p0030
  have p0032 :=
    @g_f1ofo (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0033 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      p0028 p0032
  have p0034 :=
    @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0035 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      p0033 p0034
  have p0036 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) p0035
  have p0037 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_c2nd) (.cv u))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0031 p0036
  have p0038 :=
    @g_f1oeq23 (syn_cfv (syn_c2nd) (.cv u))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0039 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classEq (syn_cfv (syn_c2nd) (.cv u))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0037 p0038
  have p0040 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0028 p0039
  have p0041 :=
    @g_f1ocnv (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0042 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0040 p0041
  have p0043 :=
    @g_simpl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0044 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0021
      p0043
  have p0045 :=
    @g_breq2d (.classMem (.cv u) (syn_chwcn D))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0030
  have p0046 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0044
      p0045
  have p0047 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0042 p0046
  have p0049 :=
    @g_biid
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0050 :=
    @g_a1i
      (syn_wb (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0049
  have p0051 := @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0052 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
      (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cwe) p0051
  have p0053 :=
    @g_anbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0050 p0052
  have p0055 :=
    @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
      (syn_cfv (syn_c1st) (.cv u))
      (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0051
  have p0056 :=
    @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0055
  have p0057 :=
    (Nominal.classEqRefl
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)))
  have p0058 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_ccom
        (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0057
  have p0060 :=
    @g_eqcomi
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0002
  have p0061 :=
    @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom
        (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      p0056 p0058 p0060
  have p0062 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0061
  have p0063 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0053 p0062
  have p0065 := @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrncndndv_1 p0019
  have p0066 := @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0065
  have p0067 :=
    @g_f1oeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0068 :=
    @g_id (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0069 :=
    @g_breq2d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r) (syn_cwe) p0068
  have p0070 :=
    @g_anbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv r) (syn_cwe) (.cv y))
      (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0067 p0069
  have p0071 :=
    @g_biid
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0072 :=
    @g_a1i
      (syn_wb (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0071
  have p0073 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0070 p0072
  have p0076 := @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0065
  have p0077 :=
    @g_f1oeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0078 := @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
  have p0079 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0078
  have p0080 :=
    @g_anbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0077 p0079
  have p0081 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0082 :=
    @g_breq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe)
      p0081
  have p0083 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (.cv x))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0080 p0082
  have p0086 := @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0065
  have p0087 :=
    @g_f1oeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0089 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0078
  have p0090 :=
    @g_anbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (.cv f) (.cv x) (.cv y))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0087 p0089
  have p0091 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0092 :=
    @g_cnveqd (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0091
  have p0093 :=
    @g_coeq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccnv (.cv f)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv r) p0092
  have p0095 :=
    @g_coeq12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom (syn_ccnv (.cv f)) (.cv r))
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
      (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0093 p0091
  have p0096 := (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r)))
  have p0097 :=
    @g_eqcomi (syn_cpwpull (.cv f) (.cv r))
      (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0096
  have p0100 :=
    @g_n_3eqtr3g (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f))
      (syn_ccom
        (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (.cv f) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0095
      p0097 p0058
  have p0101 :=
    @g_breq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (.cv f) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (.cv x)
      (syn_cwe) p0100
  have p0102 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (.cv x))
      p0090 p0101
  have p0103 :=
    @g_pwpullwesetimpndv x y f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0104 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x)))
      (.imp (syn_wa
          (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (.cv x)))
      f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0007 dv_cache_0008
      p0086 p0102 p0103
  have p0105 :=
    @g_vtocl
      (.imp (syn_wa
          (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (.cv x)))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0009 dv_cache_0010
      p0076 p0083 p0104
  have p0106 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0011 dv_cache_0012
      p0066 p0073 p0105
  have p0107 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cfv (syn_c1st) (.cv u)))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0013 dv_cache_0014 p0018 p0063 p0106
  have p0108 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0047 p0107
  have p0109 :=
    @g_syl5eqbrr (.classMem (.cv u) (syn_chwcn D))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0006 p0108
  have p0110 := @g_imassrn F (syn_cfv (syn_c2nd) (.cv u))
  have p0111 := @g_f1ofo D E F
  have p0112 := Nominal.mp hyp_hncodetrncndndv_2 p0111
  have p0113 := @g_forn D E F
  have p0114 := Nominal.mp p0112 p0113
  have p0115 :=
    @g_sseqtri (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn F) E p0110 p0114
  have p0116 :=
    @g_syl6eqss (.classMem (.cv u) (syn_chwcn D))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) E p0035 p0115
  have p0117 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E) p0109 p0116
  have p0121 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0065
      p0018
  have p0125 :=
    @g_coex
      (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0121 p0086
  have p0129 :=
    @g_elhwcodesclndv
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E p0125 p0076
  have p0130 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E))
      (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E))
      p0117 p0129
  have p0136 :=
    @g_eqcomi
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0006
  have p0137 :=
    @g_f1ofo (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0138 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0042 p0137
  have p0140 :=
    @g_biid
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0141 :=
    @g_a1i
      (syn_wb (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0140
  have p0150 :=
    @g_sseq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0061
  have p0151 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0141 p0150
  have p0155 :=
    @g_foeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0156 :=
    @g_biid
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
  have p0157 :=
    @g_a1i
      (syn_wb (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0156
  have p0158 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0155 p0157
  have p0162 :=
    @g_foeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0165 :=
    @g_xpeq12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0081 p0081
  have p0166 :=
    @g_sseq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cxp (.cv x) (.cv x))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0165
  have p0167 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (.cv x) (.cv x)))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0162 p0166
  have p0171 :=
    @g_foeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0182 :=
    @g_sseq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (.cv f) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cxp (.cv x) (.cv x)) p0100
  have p0183 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (.cv f) (.cv x) (.cv y))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (.cv x) (.cv x)))
      p0171 p0182
  have p0184 :=
    @g_pwpullssxpsetimpndv x y f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0185 :=
    @g_vtocl
      (.imp (syn_wfo (.cv f) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (.cv x) (.cv x))))
      f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0007 dv_cache_0015
      p0086 p0183 p0184
  have p0186 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (.cv x) (.cv x))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0009 dv_cache_0016
      p0076 p0167 p0185
  have p0187 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0011 dv_cache_0017
      p0066 p0158 p0186
  have p0188 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cfv (syn_c1st) (.cv u)))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0013 dv_cache_0018 p0018 p0151 p0187
  have p0189 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0138 p0188
  have p0190 :=
    @g_syl5eqss (.classMem (.cv u) (syn_chwcn D))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0136 p0189
  have p0202 :=
    @g_opfv1st
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0125 p0076
  have p0214 :=
    @g_opfv2nd
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0125 p0076
  have p0227 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0214 p0214
  have p0228 :=
    @g_sseq12i
      (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop
            (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0202 p0227
  have p0229 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wss (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop
              (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))))
      p0190 p0228
  have p0230 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop
              (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))))
      p0130 p0229
  have p0242 :=
    @g_opex
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0125 p0076
  have p0243 :=
    @g_elhwcncl E
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0244 := Nominal.mp p0242 p0243
  have p0245 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) (syn_wss
          (syn_cfv (syn_c1st) (syn_cop (syn_ccom
                (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd)
              (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                    (syn_cfv (syn_c1st) (.cv u)))
                  (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
                (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd)
              (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                    (syn_cfv (syn_c1st) (.cv u)))
                  (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
                (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcn E))
      p0230 p0244
  have p0246 :=
    @g_syl5eqel (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chncodetrnfn F) (.cv u))
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_chwcn E) p0001 p0245
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

@[expose]
noncomputable def g_hnqinctrnvaldndv (u : Var) (A : Class) (D : Class) (E : Class)
    (F : Class) (hyp_hnqinctrnvaldndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hnqinctrnvaldndv_2 : Nominal.NPrf (syn_wf1o F D E))
    (hyp_hnqinctrnvaldndv_3 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqinctrnvaldndv_4 : Nominal.NPrf (syn_wss E A))
    (hyp_hnqinctrnvaldndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn D))
        (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D)))
          (syn_cfv (syn_chnqinc E A)
            (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))))) :=
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
  have dv_cache_0001 : x ∉ ((syn_csn (.cv u))).fv := by
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
      ((syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D))
            (syn_csn (.cv u))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A)
            (syn_cec (.cv u) (syn_chwniso A))))).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cec (.cv u) (syn_chwniso D))).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cec (.cv u) (syn_chwniso A))).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_chnqmap1 A)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_ccnv (syn_chnqmap1 D))).fv :=
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
  have dv_cache_0013 : f ∉ ((syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
              (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cwe) (.cv x)))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
            (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
  have dv_cache_0017 : y ∉ ((syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr (.cv r) (syn_cwe)
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
  have dv_cache_0019 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv :=
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
      ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
              (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
          (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cxp (.cv x) (.cv x))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
            (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
      ((Wff.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
            (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
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
  have dv_cache_0025 : r ∉ ((syn_cvv)).fv :=
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
      ((Wff.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u))))
          (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))).fv :=
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
    r ∉ ((Wff.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))).fv :=
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
  have dv_cache_0028 : f ∉ ((syn_cres F (syn_cfv (syn_c2nd) (.cv u)))).fv :=
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
  have dv_cache_0029 : f ∉ ((syn_chwbij)).fv :=
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
      ((syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen)
              (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
            (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))).fv :=
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
    f ∉ ((Wff.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))).fv :=
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
    r ∉ ((Wff.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))).fv :=
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
  have dv_cache_0033 : f ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0038 : v ∉ ((syn_cfv (syn_chncodetrnfn F) (.cv u))).fv :=
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
      ((syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
          (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
              (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
            (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
                (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
                  (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))))).fv :=
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
  have dv_cache_0040 : x ∉ ((syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))).fv :=
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
      ((syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
            (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
          (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
            (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))).fv :=
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
    x ∉ ((syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))).fv :=
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
    x ∉ ((syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))).fv :=
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
  have dv_cache_0044 : x ∉ ((syn_ccnv (syn_chnqmap1 E))).fv :=
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
  have p0000 := @g_f1odm D E F
  have p0001 := Nominal.mp hyp_hnqinctrnvaldndv_2 p0000
  have p0002 := @g_dmex F hyp_hnqinctrnvaldndv_1
  have p0003 := @g_eqeltrri (syn_cdm F) D (syn_cvv) p0001 p0002
  have p0004 := @g_hnqmap1valcl D (.cv u) p0003
  have p0005 := @g_id (.classMem (.cv u) (syn_chwcn D))
  have p0006 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D))
        (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (.cv u)))
          (syn_cec (.cv u) (syn_chwniso D))))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0004
      p0005
  have p0007 := @g_snelpw1 (.cv u) (syn_chwcn D)
  have p0008 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn D))) p0005 p0007
  have p0009 := @g_hnqmap1fn D p0003
  have p0010 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn D)))
      (syn_wfn (syn_chnqmap1 D) (syn_cpw1 (syn_chwcn D))) p0008 p0009
  have p0011 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn D)) (syn_csn (.cv u))
      (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqmap1 D)
  have p0012 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnqmap1 D) (syn_cpw1 (syn_chwcn D)))
        (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn D))))
      (syn_wb (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (.cv u)))
          (syn_cec (.cv u) (syn_chwniso D)))
        (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 D) (syn_cec (.cv u) (syn_chwniso D))))
      p0010 p0011
  have p0013 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 D) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso D)))
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 D) (syn_cec (.cv u) (syn_chwniso D))) p0006
      p0012
  have p0014 :=
    @g_brcnv (syn_cec (.cv u) (syn_chwniso D)) (syn_csn (.cv u)) (syn_chnqmap1 D)
  have p0015 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 D) (syn_cec (.cv u) (syn_chwniso D)))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u)))
      p0013 p0014
  have p0016 := @g_hwcnssbase A D hyp_hnqinctrnvaldndv_3
  have p0017 := @g_ssel (syn_chwcn D) (syn_chwcn A) (.cv u)
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A)))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0018
      p0005
  have p0020 := @g_hnqmap1valcl A (.cv u) hyp_hnqinctrnvaldndv_5
  have p0021 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)))
      p0019 p0020
  have p0022 := @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0023 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0019 p0022
  have p0024 := @g_hnqmap1fn A hyp_hnqinctrnvaldndv_5
  have p0025 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)))
      (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) p0023 p0024
  have p0026 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn A)) (syn_csn (.cv u))
      (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqmap1 A)
  have p0027 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)))
        (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))))
      (syn_wb (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))
          (syn_cec (.cv u) (syn_chwniso A)))
        (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))
      p0025 p0026
  have p0028 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) p0021
      p0027
  have p0029 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u)))
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) p0015
      p0028
  have p0030 := @g_snex (.cv u)
  have p0031 := @g_id (.classEq (.cv x) (syn_csn (.cv u)))
  have p0032 :=
    @g_breq2d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u))
      (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) p0031
  have p0034 :=
    @g_breq1d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u))
      (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqmap1 A) p0031
  have p0035 :=
    @g_anbi12d (.classEq (.cv x) (syn_csn (.cv u)))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (syn_csn (.cv u)))
      (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))) p0032
      p0034
  have p0036 :=
    @g_spcev
      (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x))
        (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D))
          (syn_csn (.cv u)))
        (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))
      x (syn_csn (.cv u)) dv_cache_0001 dv_cache_0002 p0030 p0035
  have p0037 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D))
          (syn_csn (.cv u)))
        (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wex x (syn_wa
          (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x))
          (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))))
      p0029 p0036
  have p0038 :=
    @g_brco x (syn_cec (.cv u) (syn_chwniso D)) (syn_cec (.cv u) (syn_chwniso A))
      (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0039 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wex x (syn_wa
          (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_ccnv (syn_chnqmap1 D)) (.cv x))
          (syn_wbr (.cv x) (syn_chnqmap1 A) (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D))
        (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0037 p0038
  have p0040 := (Nominal.classEqRefl (syn_chnqinc D A))
  have p0041 :=
    @g_breqi (syn_cec (.cv u) (syn_chwniso D)) (syn_cec (.cv u) (syn_chwniso A))
      (syn_chnqinc D A) (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D))) p0040
  have p0042 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D))
        (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 D)))
        (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A)
        (syn_cec (.cv u) (syn_chwniso A)))
      p0039 p0041
  have p0043 := @g_hwnisoclasselhnordcl D (.cv u) p0003
  have p0044 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D))
        (.classMem (syn_cec (.cv u) (syn_chwniso D)) (syn_chnord D)))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0043
      p0005
  have p0045 := @g_hnqincfn A D hyp_hnqinctrnvaldndv_3 p0003 hyp_hnqinctrnvaldndv_5
  have p0046 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cec (.cv u) (syn_chwniso D)) (syn_chnord D))
      (syn_wfn (syn_chnqinc D A) (syn_chnord D)) p0044 p0045
  have p0047 :=
    @g_fnbrfvb (syn_chnord D) (syn_cec (.cv u) (syn_chwniso D))
      (syn_cec (.cv u) (syn_chwniso A)) (syn_chnqinc D A)
  have p0048 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnqinc D A) (syn_chnord D))
        (.classMem (syn_cec (.cv u) (syn_chwniso D)) (syn_chnord D)))
      (syn_wb (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D)))
          (syn_cec (.cv u) (syn_chwniso A)))
        (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A)
          (syn_cec (.cv u) (syn_chwniso A))))
      p0046 p0047
  have p0049 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D)))
        (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A)
        (syn_cec (.cv u) (syn_chwniso A)))
      p0042 p0048
  have p0050 := @g_ssv D
  have p0051 := @g_hwcnssbase (syn_cvv) D p0050
  have p0052 := @g_ssel (syn_chwcn D) (syn_chwcn (syn_cvv)) (.cv u)
  have p0053 := Nominal.mp p0051 p0052
  have p0054 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn (syn_cvv))))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0053
      p0005
  have p0055 := @g_vex u
  have p0056 := @g_hncodetrnfnvalndv u F hyp_hnqinctrnvaldndv_1 p0055
  have p0057 :=
    (Nominal.classEqRefl (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u))))
  have p0058 := @g_cnvcnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0059 :=
    @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0058
  have p0060 :=
    @g_coeq1i
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0059
  have p0061 :=
    @g_eqtri
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0057 p0060
  have p0062 := @g_hwcnpair u D
  have p0063 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classEq (.cv u)
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0062
      p0005
  have p0065 := @g_elhwcncl D (.cv u)
  have p0066 := Nominal.mp p0055 p0065
  have p0067 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0066
  have p0068 :=
    @g_a1ii
      (.imp (.classMem (.cv u) (syn_chwcn D)) (syn_wa (.classMem (.cv u) (syn_chwcodes D))
          (syn_wss (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn D))) p0067
      p0005
  have p0069 :=
    @g_simpl (.classMem (.cv u) (syn_chwcodes D))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
  have p0070 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcodes D)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (.cv u) (syn_chwcodes D)) p0068 p0069
  have p0071 :=
    @g_eqeltrrd (.classMem (.cv u) (syn_chwcn D)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes D)
      p0063 p0070
  have p0072 := @g_fvex (.cv u) (syn_c1st)
  have p0073 := @g_fvex (.cv u) (syn_c2nd)
  have p0074 :=
    @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) D p0072
      p0073
  have p0075 :=
    @g_sylib (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      p0071 p0074
  have p0076 :=
    @g_simpr (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0077 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D) p0075 p0076
  have p0078 := @g_f1of1 D E F
  have p0079 := Nominal.mp hyp_hnqinctrnvaldndv_2 p0078
  have p0080 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
      (syn_wf1 F D E) p0077 p0079
  have p0081 := @g_f1ores D E (syn_cfv (syn_c2nd) (.cv u)) F
  have p0082 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wf1 F D E) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      p0080 p0081
  have p0083 :=
    @g_f1odm (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0084 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c2nd) (.cv u)))
      p0082 p0083
  have p0085 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      p0084
  have p0086 :=
    @g_f1ofo (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0087 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      p0082 p0086
  have p0088 :=
    @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0089 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wfo (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      p0087 p0088
  have p0090 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) p0089
  have p0091 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_c2nd) (.cv u))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0085 p0090
  have p0092 :=
    @g_f1oeq23 (syn_cfv (syn_c2nd) (.cv u))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0093 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classEq (syn_cfv (syn_c2nd) (.cv u))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (.classEq (syn_cima F (syn_cfv (syn_c2nd) (.cv u)))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wb (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0091 p0092
  have p0094 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0082 p0093
  have p0095 :=
    @g_f1ocnv (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
  have p0096 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0094 p0095
  have p0097 :=
    @g_simpl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D)
  have p0098 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0075
      p0097
  have p0099 :=
    @g_breq2d (.classMem (.cv u) (syn_chwcn D))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) p0084
  have p0100 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) p0098
      p0099
  have p0101 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0096 p0100
  have p0103 :=
    @g_biid
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0104 :=
    @g_a1i
      (syn_wb (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0103
  have p0105 := @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0106 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
      (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cwe) p0105
  have p0107 :=
    @g_anbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0104 p0106
  have p0109 :=
    @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
      (syn_cfv (syn_c1st) (.cv u))
      (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0105
  have p0110 :=
    @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0109
  have p0111 :=
    (Nominal.classEqRefl
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)))
  have p0112 :=
    @g_eqcomi (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_ccom
        (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0111
  have p0114 :=
    @g_eqcomi
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0057
  have p0115 :=
    @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom
        (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      p0110 p0112 p0114
  have p0116 :=
    @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0115
  have p0117 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0107 p0116
  have p0119 := @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hnqinctrnvaldndv_1 p0073
  have p0120 := @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0119
  have p0121 :=
    @g_f1oeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0122 :=
    @g_id (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0123 :=
    @g_breq2d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r) (syn_cwe) p0122
  have p0124 :=
    @g_anbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (.cv r) (syn_cwe) (.cv y))
      (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0121 p0123
  have p0125 :=
    @g_biid
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0126 :=
    @g_a1i
      (syn_wb (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0125
  have p0127 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0124 p0126
  have p0130 := @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0119
  have p0131 :=
    @g_f1oeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0132 := @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
  have p0133 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0132
  have p0134 :=
    @g_anbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0131 p0133
  have p0135 :=
    @g_id (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0136 :=
    @g_breq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (syn_cwe)
      p0135
  have p0137 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (.cv x))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0134 p0136
  have p0140 := @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0119
  have p0141 :=
    @g_f1oeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0143 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0132
  have p0144 :=
    @g_anbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wf1o (.cv f) (.cv x) (.cv y))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0141 p0143
  have p0145 :=
    @g_id (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0146 :=
    @g_cnveqd (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0145
  have p0147 :=
    @g_coeq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccnv (.cv f)) (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv r) p0146
  have p0149 :=
    @g_coeq12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom (syn_ccnv (.cv f)) (.cv r))
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
      (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0147 p0145
  have p0150 := (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r)))
  have p0151 :=
    @g_eqcomi (syn_cpwpull (.cv f) (.cv r))
      (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0150
  have p0154 :=
    @g_n_3eqtr3g (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f))
      (syn_ccom
        (syn_ccom (syn_ccnv (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (.cv f) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0149
      p0151 p0112
  have p0155 :=
    @g_breq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (.cv f) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) (.cv x)
      (syn_cwe) p0154
  have p0156 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)))
      (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cwe) (.cv x))
      p0144 p0155
  have p0157 :=
    @g_pwpullwesetimpndv x y f r dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012
  have p0158 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x)))
      (.imp (syn_wa
          (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (.cv x)))
      f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0013 dv_cache_0014
      p0140 p0156 p0157
  have p0159 :=
    @g_vtocl
      (.imp (syn_wa
          (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (.cv x)))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0015 dv_cache_0016
      p0130 p0137 p0158
  have p0160 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
          (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0017 dv_cache_0018
      p0120 p0127 p0159
  have p0161 :=
    @g_vtocl
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
            (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cfv (syn_c1st) (.cv u)))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0019 dv_cache_0020 p0072 p0117 p0160
  have p0162 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wbr (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0101 p0161
  have p0163 :=
    @g_syl5eqbrr (.classMem (.cv u) (syn_chwcn D))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0061 p0162
  have p0164 := @g_imassrn F (syn_cfv (syn_c2nd) (.cv u))
  have p0165 := @g_f1ofo D E F
  have p0166 := Nominal.mp hyp_hnqinctrnvaldndv_2 p0165
  have p0167 := @g_forn D E F
  have p0168 := Nominal.mp p0166 p0167
  have p0169 :=
    @g_sseqtri (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) (syn_crn F) E p0164 p0168
  have p0170 :=
    @g_syl6eqss (.classMem (.cv u) (syn_chwcn D))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cima F (syn_cfv (syn_c2nd) (.cv u))) E p0089 p0169
  have p0171 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E) p0163 p0170
  have p0175 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0119
      p0072
  have p0179 :=
    @g_coex
      (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0175 p0140
  have p0183 :=
    @g_elhwcodesclndv
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E p0179 p0130
  have p0184 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cwe) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wss (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) E))
      (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E))
      p0171 p0183
  have p0190 :=
    @g_eqcomi
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0061
  have p0191 :=
    @g_f1ofo (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0192 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0096 p0191
  have p0194 :=
    @g_biid
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0195 :=
    @g_a1i
      (syn_wb (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0194
  have p0204 :=
    @g_sseq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0115
  have p0205 :=
    @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0195 p0204
  have p0209 :=
    @g_foeq3 (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0210 :=
    @g_biid
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
  have p0211 :=
    @g_a1i
      (syn_wb (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0210
  have p0212 :=
    @g_imbi12d (.classEq (.cv y) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0209 p0211
  have p0216 :=
    @g_foeq2 (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)
      (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0219 :=
    @g_xpeq12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0135 p0135
  have p0220 :=
    @g_sseq2d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cxp (.cv x) (.cv x))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)) p0219
  have p0221 :=
    @g_imbi12d (.classEq (.cv x) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (.cv x) (.cv x)))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0216 p0220
  have p0225 :=
    @g_foeq1 (.cv x) (.cv y) (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0236 :=
    @g_sseq1d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (.cv f) (.cv r))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
      (syn_cxp (.cv x) (.cv x)) p0154
  have p0237 :=
    @g_imbi12d (.classEq (.cv f) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wfo (.cv f) (.cv x) (.cv y))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
      (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
        (syn_cxp (.cv x) (.cv x)))
      p0225 p0236
  have p0238 :=
    @g_pwpullssxpsetimpndv x y f r dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012
  have p0239 :=
    @g_vtocl
      (.imp (syn_wfo (.cv f) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (.cv x) (.cv x))))
      f (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0013 dv_cache_0021
      p0140 p0237 p0238
  have p0240 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
        (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (.cv x) (.cv x))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      x (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0015 dv_cache_0022
      p0130 p0221 p0239
  have p0241 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      y (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0017 dv_cache_0023
      p0120 p0212 p0240
  have p0242 :=
    @g_vtocl
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (.imp (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
          (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_cfv (syn_c1st) (.cv u)))
          (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      r (syn_cfv (syn_c1st) (.cv u)) dv_cache_0019 dv_cache_0024 p0072 p0205 p0241
  have p0243 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wfo (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wss (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_cfv (syn_c1st) (.cv u)))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      p0192 p0242
  have p0244 :=
    @g_syl5eqss (.classMem (.cv u) (syn_chwcn D))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cpwpull (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0190 p0243
  have p0256 :=
    @g_opfv1st
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0179 p0130
  have p0268 :=
    @g_opfv2nd
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0179 p0130
  have p0281 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0268 p0268
  have p0282 :=
    @g_sseq12i
      (syn_cfv (syn_c1st) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop
            (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0256 p0281
  have p0283 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wss (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cxp (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop
              (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))))
      p0244 p0282
  have p0284 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E))
      (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_ccom
              (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd) (syn_cop
              (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))))
      p0184 p0283
  have p0296 :=
    @g_opex
      (syn_ccom
        (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
        (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0179 p0130
  have p0297 :=
    @g_elhwcncl E
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
  have p0298 := Nominal.mp p0296 p0297
  have p0299 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                (syn_cfv (syn_c1st) (.cv u)))
              (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcodes E)) (syn_wss
          (syn_cfv (syn_c1st) (syn_cop (syn_ccom
                (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                  (syn_cfv (syn_c1st) (.cv u)))
                (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cfv (syn_c2nd)
              (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                    (syn_cfv (syn_c1st) (.cv u)))
                  (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
                (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cfv (syn_c2nd)
              (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
                    (syn_cfv (syn_c1st) (.cv u)))
                  (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
                (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))))))
      (.classMem (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_chwcn E))
      p0284 p0298
  have p0300 :=
    @g_syl5eqel (.classMem (.cv u) (syn_chwcn D)) (syn_cfv (syn_chncodetrnfn F) (.cv u))
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_chwcn E) p0056 p0299
  have p0301 := @g_ssv E
  have p0302 := @g_hwcnssbase (syn_cvv) E p0301
  have p0303 :=
    @g_ssel (syn_chwcn E) (syn_chwcn (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u))
  have p0304 := Nominal.mp p0302 p0303
  have p0305 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) p0300 p0304
  have p0306 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn (syn_cvv)))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) p0054 p0305
  have p0309 := @g_hwbijf1oclndv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0119
  have p0310 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wf1o (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij)) p0094 p0309
  have p0314 :=
    @g_hwgenvalclndv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
      (syn_cfv (syn_c1st) (.cv u)) p0119 p0072
  have p0315 :=
    @g_opeq2d (.classMem (.cv u) (syn_chwcn D))
      (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) p0084
  have p0316 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn D)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0063
  have p0317 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn D))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (.cv u) p0315
      p0316
  have p0318 :=
    @g_opeq1d (.classMem (.cv u) (syn_chwcn D))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (.cv u)
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0317
  have p0321 :=
    @g_eqcomi (syn_cfv (syn_chncodetrnfn F) (.cv u))
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      p0056
  have p0322 :=
    @g_opeq2i
      (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_cfv (syn_chncodetrnfn F) (.cv u)) (.cv u) p0321
  have p0323 :=
    @g_syl6eq (.classMem (.cv u) (syn_chwcn D))
      (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom
            (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (.cv u) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
              (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0318 p0322
  have p0324 :=
    @g_syl5eq (.classMem (.cv u) (syn_chwcn D))
      (syn_cfv (syn_chwgen)
        (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u))
          (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom
            (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
            (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0314 p0323
  have p0326 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))))
        (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      (.classMem (syn_cfv (syn_c1st) (.cv u)) (syn_cvv)) p0324 p0072
  have p0328 :=
    @g_opeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
      (syn_cfv (syn_c1st) (.cv u)) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0105
  have p0329 :=
    @g_fveq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r))
      (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
      (syn_chwgen) p0328
  have p0330 :=
    @g_eqeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
      (syn_cfv (syn_chwgen)
        (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0329
  have p0331 :=
    @g_rspcev
      (.classEq
        (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
        (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))
            (syn_cfv (syn_c1st) (.cv u))))
        (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      r (syn_cfv (syn_c1st) (.cv u)) (syn_cvv) dv_cache_0019 dv_cache_0025 dv_cache_0026
      p0330
  have p0332 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (syn_cfv (syn_c1st) (.cv u)) (syn_cvv)) (.classEq (syn_cfv (syn_chwgen)
            (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))))
          (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))
      (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen)
            (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
          (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))
      p0326 p0331
  have p0333 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij))
      (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen)
            (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
          (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))
      p0310 p0332
  have p0334 := @g_id (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
  have p0335 :=
    @g_opeq1d (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) (.cv f)
      (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r) p0334
  have p0336 :=
    @g_fveq2d (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cop (.cv f) (.cv r))
      (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)) (syn_chwgen) p0335
  have p0337 :=
    @g_eqeq1d (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
      (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
      (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0336
  have p0338 :=
    @g_rexbidv (.classEq (.cv f) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      (.classEq
        (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
        (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      r (syn_cvv) dv_cache_0027 p0337
  have p0339 :=
    @g_rspcev
      (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
          (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))
      (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen)
            (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
          (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))
      f (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij) dv_cache_0028 dv_cache_0029
      dv_cache_0030 p0338
  have p0340 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_chwbij))
        (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen)
              (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (.cv r)))
            (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))
      p0333 p0339
  have p0341 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))
      p0306 p0340
  have p0342 := @g_elex (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))
  have p0343 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cvv)) p0305 p0342
  have p0344 := @g_id (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
  have p0345 :=
    @g_breq2d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.cv v)
      (syn_cfv (syn_chncodetrnfn F) (.cv u)) (.cv u) (syn_chwniso (syn_cvv)) p0344
  have p0346 := @g_biid (.classMem (.cv u) (syn_chwcn (syn_cvv)))
  have p0347 :=
    @g_a1i
      (syn_wb (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classMem (.cv u) (syn_chwcn (syn_cvv))))
      (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0346
  have p0349 :=
    @g_eleq1d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.cv v)
      (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv)) p0344
  have p0350 :=
    @g_anbi12d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (.classMem (.cv u) (syn_chwcn (syn_cvv))) (.classMem (.cv u) (syn_chwcn (syn_cvv)))
      (.classMem (.cv v) (syn_chwcn (syn_cvv)))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))) p0347 p0349
  have p0352 :=
    @g_opeq2d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u))) (.cv v)
      (syn_cfv (syn_chncodetrnfn F) (.cv u)) (.cv u) p0344
  have p0353 :=
    @g_eqeq2d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_cop (.cv u) (.cv v)) (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) p0352
  have p0354 :=
    @g_n_2rexbidv (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))
      (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
        (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      f r (syn_chwbij) (syn_cvv) dv_cache_0031 dv_cache_0032 p0353
  have p0355 :=
    @g_anbi12d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classMem (.cv v) (syn_chwcn (syn_cvv))))
      (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
        (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (.cv v)))))
      (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
          (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
            (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))
      p0350 p0354
  have p0356 :=
    @g_bibi12d (.classEq (.cv v) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
          (.classMem (.cv v) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij)
          (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (.cv v))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
          (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))))
      p0345 p0355
  have p0357 :=
    @g_elhwnisogen v u (syn_cvv) f r dv_cache_0033 dv_cache_0025 dv_cache_0007
      dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
  have p0358 :=
    @g_vtoclg
      (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
            (.classMem (.cv v) (syn_chwcn (syn_cvv)))) (syn_wrex f (syn_chwbij)
            (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
                (syn_cop (.cv u) (.cv v)))))))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
        (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
            (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
          (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
              (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
                (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))))
      v (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cvv) dv_cache_0038 dv_cache_0039 p0356
      p0357
  have p0359 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cvv))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
        (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
            (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
          (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
              (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
                (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))))))))
      p0343 p0358
  have p0360 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn (syn_cvv)))
          (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn (syn_cvv))))
        (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv)
            (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r)))
              (syn_cop (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)))))))
      p0341 p0359
  have p0361 := @g_hwcnssbase A E hyp_hnqinctrnvaldndv_4
  have p0362 := @g_ssel (syn_chwcn E) (syn_chwcn A) (syn_cfv (syn_chncodetrnfn F) (.cv u))
  have p0363 := Nominal.mp p0361 p0362
  have p0364 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)) p0300 p0363
  have p0365 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D)) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)) p0019 p0364
  have p0366 := @g_ssv A
  have p0367 :=
    @g_hwnisobasebicl (syn_cvv) (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u)) A p0366
  have p0368 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
        (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      p0365 p0367
  have p0369 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (.cv u) (syn_chwniso (syn_cvv)) (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0360 p0368
  have p0370 :=
    @g_hwnisoclasseqbcl A (.cv u) (syn_cfv (syn_chncodetrnfn F) (.cv u))
      hyp_hnqinctrnvaldndv_5
  have p0371 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (.cv u) (syn_chwniso A))
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
        (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      p0365 p0370
  have p0372 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cec (.cv u) (syn_chwniso A))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      (syn_wbr (.cv u) (syn_chwniso A) (syn_cfv (syn_chncodetrnfn F) (.cv u))) p0369 p0371
  have p0373 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn D))
      (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D)))
      (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) p0049 p0372
  have p0378 := @g_rnex F hyp_hnqinctrnvaldndv_1
  have p0379 := @g_eqeltrri (syn_crn F) E (syn_cvv) p0168 p0378
  have p0380 := @g_hnqmap1valcl E (syn_cfv (syn_chncodetrnfn F) (.cv u)) p0379
  have p0381 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))
      (.classEq (syn_cfv (syn_chnqmap1 E) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
      p0300 p0380
  have p0382 := @g_snelpw1 (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)
  have p0383 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))
      (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn E)))
      p0300 p0382
  have p0384 := @g_hnqmap1fn E p0379
  have p0385 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn E)))
      (syn_wfn (syn_chnqmap1 E) (syn_cpw1 (syn_chwcn E))) p0383 p0384
  have p0386 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqmap1 E)
  have p0387 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnqmap1 E) (syn_cpw1 (syn_chwcn E)))
        (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn E))))
      (syn_wb (.classEq
          (syn_cfv (syn_chnqmap1 E) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
        (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))))
      p0385 p0386
  have p0388 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 E) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
      p0381 p0387
  have p0389 :=
    @g_brcnv (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
      (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E)
  have p0390 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 E)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      p0388 p0389
  have p0391 :=
    @g_hnqmap1valcl A (syn_cfv (syn_chncodetrnfn F) (.cv u)) hyp_hnqinctrnvaldndv_5
  have p0392 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0364 p0391
  have p0393 := @g_snelpw1 (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A)
  have p0394 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn A))
      (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn A)))
      p0364 p0393
  have p0396 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn A)))
      (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) p0394 p0024
  have p0397 :=
    @g_fnbrfvb (syn_cpw1 (syn_chwcn A)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqmap1 A)
  have p0398 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)))
        (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_cpw1 (syn_chwcn A))))
      (syn_wb (.classEq
          (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
        (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))
      p0396 p0397
  have p0399 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0392 p0398
  have p0400 :=
    @g_jca (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0390 p0399
  have p0401 := @g_snex (syn_cfv (syn_chncodetrnfn F) (.cv u))
  have p0402 := @g_id (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
  have p0403 :=
    @g_breq2d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.cv x)
      (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
      (syn_ccnv (syn_chnqmap1 E)) p0402
  have p0405 :=
    @g_breq1d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))) (.cv x)
      (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u)))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqmap1 A)
      p0402
  have p0406 :=
    @g_anbi12d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_ccnv (syn_chnqmap1 E)) (.cv x))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
      (syn_wbr (.cv x) (syn_chnqmap1 A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0403 p0405
  have p0407 :=
    @g_spcev
      (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
          (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))
      (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
          (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
        (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))
      x (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) dv_cache_0040 dv_cache_0041 p0401
      p0406
  have p0408 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
          (syn_ccnv (syn_chnqmap1 E)) (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))))
        (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn F) (.cv u))) (syn_chnqmap1 A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))
      (syn_wex x (syn_wa
          (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
            (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A)
            (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))))
      p0400 p0407
  have p0409 :=
    @g_brco x (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqmap1 A)
      (syn_ccnv (syn_chnqmap1 E)) dv_cache_0042 dv_cache_0043 dv_cache_0005 dv_cache_0044
  have p0410 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wex x (syn_wa
          (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
            (syn_ccnv (syn_chnqmap1 E)) (.cv x)) (syn_wbr (.cv x) (syn_chnqmap1 A)
            (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E)))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0408 p0409
  have p0411 := (Nominal.classEqRefl (syn_chnqinc E A))
  have p0412 :=
    @g_breqi (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqinc E A)
      (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E))) p0411
  have p0413 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn D))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_ccom (syn_chnqmap1 A) (syn_ccnv (syn_chnqmap1 E)))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0410 p0412
  have p0414 := @g_hwnisoclasselhnordcl E (syn_cfv (syn_chncodetrnfn F) (.cv u)) p0379
  have p0415 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))
      (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_chnord E))
      p0300 p0414
  have p0416 := @g_hnqincfn A E hyp_hnqinctrnvaldndv_4 p0379 hyp_hnqinctrnvaldndv_5
  have p0417 :=
    @g_jctil (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_chnord E))
      (syn_wfn (syn_chnqinc E A) (syn_chnord E)) p0415 p0416
  have p0418 :=
    @g_fnbrfvb (syn_chnord E)
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)) (syn_chnqinc E A)
  have p0419 :=
    @g_syl (.classMem (.cv u) (syn_chwcn D))
      (syn_wa (syn_wfn (syn_chnqinc E A) (syn_chnord E))
        (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
          (syn_chnord E)))
      (syn_wb (.classEq (syn_cfv (syn_chnqinc E A)
            (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
        (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
          (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))))
      p0417 p0418
  have p0420 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqinc E A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_chnqinc E A) (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A)))
      p0413 p0419
  have p0421 :=
    @g_eqtr4d (.classMem (.cv u) (syn_chwcn D))
      (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D)))
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso A))
      (syn_cfv (syn_chnqinc E A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
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

@[expose]
noncomputable def g_hnqinctrnrnssndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hnqinctrnrnssndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hnqinctrnrnssndv_2 : Nominal.NPrf (syn_wf1o F D E))
    (hyp_hnqinctrnrnssndv_3 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqinctrnrnssndv_4 : Nominal.NPrf (syn_wss E A))
    (hyp_hnqinctrnrnssndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wss (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A))) :=
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
  have dv_cache_0002 : x ∉ ((syn_chnqinc D A)).fv :=
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
  have dv_cache_0006 : u ∉ ((Wff.classMem (.cv y) (syn_crn (syn_chnqinc E A)))).fv :=
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
  have dv_cache_0007 : u ∉ ((syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))).fv :=
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
  have dv_cache_0008 : x ∉ ((Wff.classMem (.cv y) (syn_crn (syn_chnqinc E A)))).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_crn (syn_chnqinc D A))).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_crn (syn_chnqinc E A))).fv :=
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
  have p0000 := @g_elrn x (.cv y) (syn_chnqinc D A) dv_cache_0001 dv_cache_0002
  have p0001 := @g_breldm (.cv x) (.cv y) (syn_chnqinc D A)
  have p0002 := @g_f1odm D E F
  have p0003 := Nominal.mp hyp_hnqinctrnrnssndv_2 p0002
  have p0004 := @g_dmex F hyp_hnqinctrnrnssndv_1
  have p0005 := @g_eqeltrri (syn_cdm F) D (syn_cvv) p0003 p0004
  have p0006 := @g_hnqincdm A D hyp_hnqinctrnrnssndv_3 p0005 hyp_hnqinctrnrnssndv_5
  have p0007 := @g_eleq2i (syn_cdm (syn_chnqinc D A)) (syn_chnord D) (.cv x) p0006
  have p0008 :=
    @g_sylib (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
      (.classMem (.cv x) (syn_cdm (syn_chnqinc D A))) (.classMem (.cv x) (syn_chnord D))
      p0001 p0007
  have p0009 := @g_vex x
  have p0010 := @g_elhnord x u D dv_cache_0003 dv_cache_0004 dv_cache_0005 p0009
  have p0011 :=
    @g_id (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0012 :=
    @g_sylbi (.classMem (.cv x) (syn_chnord D))
      (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
      (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
      p0010 p0011
  have p0013 :=
    @g_syl (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)) (.classMem (.cv x) (syn_chnord D))
      (syn_wrex u (syn_chwcn D) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
      p0008 p0012
  have p0014 :=
    @g_simpr (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
      (syn_wa (.classMem (.cv u) (syn_chwcn D))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0015 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn D))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn D))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))) p0014 p0015
  have p0017 :=
    @g_fveq2d
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (.cv x) (syn_cec (.cv u) (syn_chwniso D)) (syn_chnqinc D A) p0016
  have p0018 :=
    @g_simpl (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
      (syn_wa (.classMem (.cv u) (syn_chwcn D))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
  have p0023 := @g_hnqincfn A D hyp_hnqinctrnrnssndv_3 p0005 hyp_hnqinctrnrnssndv_5
  have p0024 := @g_fnfun (syn_chnord D) (syn_chnqinc D A)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_funbrfv (.cv x) (.cv y) (syn_chnqinc D A)
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
      (.classEq (syn_cfv (syn_chnqinc D A) (.cv x)) (.cv y)) p0018 p0027
  have p0029 :=
    @g_eqtr3d
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_cfv (syn_chnqinc D A) (.cv x))
      (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (.cv y) p0017 p0028
  have p0031 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn D))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))
  have p0032 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn D))
        (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D))))
      (.classMem (.cv u) (syn_chwcn D)) p0014 p0031
  have p0033 :=
    @g_hnqinctrnvaldndv u A D E F hyp_hnqinctrnrnssndv_1 hyp_hnqinctrnrnssndv_2
      hyp_hnqinctrnrnssndv_3 hyp_hnqinctrnrnssndv_4 hyp_hnqinctrnrnssndv_5
  have p0034 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (.classMem (.cv u) (syn_chwcn D))
      (.classEq (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D)))
        (syn_cfv (syn_chnqinc E A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))))
      p0032 p0033
  have p0035 :=
    @g_eqtr3d
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_cfv (syn_chnqinc D A) (syn_cec (.cv u) (syn_chwniso D))) (.cv y)
      (syn_cfv (syn_chnqinc E A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
      p0029 p0034
  have p0036 := @g_f1ofo D E F
  have p0037 := Nominal.mp hyp_hnqinctrnrnssndv_2 p0036
  have p0038 := @g_forn D E F
  have p0039 := Nominal.mp p0037 p0038
  have p0040 := @g_rnex F hyp_hnqinctrnrnssndv_1
  have p0041 := @g_eqeltrri (syn_crn F) E (syn_cvv) p0039 p0040
  have p0042 := @g_hnqincfn A E hyp_hnqinctrnrnssndv_4 p0041 hyp_hnqinctrnrnssndv_5
  have p0043 :=
    @g_a1i (syn_wfn (syn_chnqinc E A) (syn_chnord E))
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      p0042
  have p0047 := @g_hncodetrncndndv u D E F hyp_hnqinctrnrnssndv_1 hyp_hnqinctrnrnssndv_2
  have p0048 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (.classMem (.cv u) (syn_chwcn D))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E)) p0032 p0047
  have p0055 := @g_hwnisoclasselhnordcl E (syn_cfv (syn_chncodetrnfn F) (.cv u)) p0041
  have p0056 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (.classMem (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwcn E))
      (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_chnord E))
      p0048 p0055
  have p0057 :=
    @g_jca
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_wfn (syn_chnqinc E A) (syn_chnord E))
      (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
        (syn_chnord E))
      p0043 p0056
  have p0058 :=
    @g_fnfvelrn (syn_chnord E)
      (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)) (syn_chnqinc E A)
  have p0059 :=
    @g_syl
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (syn_wa (syn_wfn (syn_chnqinc E A) (syn_chnord E))
        (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E))
          (syn_chnord E)))
      (.classMem (syn_cfv (syn_chnqinc E A)
          (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
        (syn_crn (syn_chnqinc E A)))
      p0057 p0058
  have p0060 :=
    @g_eqeltrd
      (syn_wa (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
        (syn_wa (.classMem (.cv u) (syn_chwcn D))
          (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))))
      (.cv y)
      (syn_cfv (syn_chnqinc E A)
        (syn_cec (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_chwniso E)))
      (syn_crn (syn_chnqinc E A)) p0035 p0059
  have p0061 :=
    @g_rexlimddv (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
      (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso D)))
      (.classMem (.cv y) (syn_crn (syn_chnqinc E A))) u (syn_chwcn D) dv_cache_0006
      dv_cache_0007 p0013 p0060
  have p0062 :=
    @g_exlimiv (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y))
      (.classMem (.cv y) (syn_crn (syn_chnqinc E A))) x dv_cache_0008 p0061
  have p0063 :=
    @g_sylbi (.classMem (.cv y) (syn_crn (syn_chnqinc D A)))
      (syn_wex x (syn_wbr (.cv x) (syn_chnqinc D A) (.cv y)))
      (.classMem (.cv y) (syn_crn (syn_chnqinc E A))) p0000 p0062
  have p0064 :=
    @g_ssriv y (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A)) dv_cache_0009
      dv_cache_0010 p0063
  exact p0064

@[expose]
noncomputable def g_hnqinctrnrneqndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hnqinctrnrneqndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hnqinctrnrneqndv_2 : Nominal.NPrf (syn_wf1o F D E))
    (hyp_hnqinctrnrneqndv_3 : Nominal.NPrf (syn_wss D A))
    (hyp_hnqinctrnrneqndv_4 : Nominal.NPrf (syn_wss E A))
    (hyp_hnqinctrnrneqndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A))) :=
  by
  have p0000 :=
    @g_hnqinctrnrnssndv A D E F hyp_hnqinctrnrneqndv_1 hyp_hnqinctrnrneqndv_2
      hyp_hnqinctrnrneqndv_3 hyp_hnqinctrnrneqndv_4 hyp_hnqinctrnrneqndv_5
  have p0001 := @g_cnvex F hyp_hnqinctrnrneqndv_1
  have p0002 := @g_f1ocnv D E F
  have p0003 := Nominal.mp hyp_hnqinctrnrneqndv_2 p0002
  have p0004 :=
    @g_hnqinctrnrnssndv A E D (syn_ccnv F) p0001 p0003 hyp_hnqinctrnrneqndv_4
      hyp_hnqinctrnrneqndv_3 hyp_hnqinctrnrneqndv_5
  have p0005 :=
    @g_eqssi (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_hnordf1oenambndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hnordf1oenambndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hnordf1oenambndv_2 : Nominal.NPrf (syn_wf1o F D E))
    (hyp_hnordf1oenambndv_3 : Nominal.NPrf (syn_wss D A))
    (hyp_hnordf1oenambndv_4 : Nominal.NPrf (syn_wss E A))
    (hyp_hnordf1oenambndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_chnord D) (syn_cen) (syn_chnord E)) :=
  by
  have p0000 := @g_f1odm D E F
  have p0001 := Nominal.mp hyp_hnordf1oenambndv_2 p0000
  have p0002 := @g_dmex F hyp_hnordf1oenambndv_1
  have p0003 := @g_eqeltrri (syn_cdm F) D (syn_cvv) p0001 p0002
  have p0004 := @g_hnqincf1 A D hyp_hnordf1oenambndv_3 p0003 hyp_hnordf1oenambndv_5
  have p0005 := @g_f1f1orn (syn_chnord D) (syn_chnord A) (syn_chnqinc D A)
  have p0006 := Nominal.mp p0004 p0005
  have p0011 :=
    @g_pm3_2i (.classMem D (syn_cvv)) (.classMem A (syn_cvv)) p0003 hyp_hnordf1oenambndv_5
  have p0012 := @g_hnqincexg A D
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_f1oen (syn_chnord D) (syn_crn (syn_chnqinc D A)) (syn_chnqinc D A) p0013
  have p0015 := Nominal.mp p0006 p0014
  have p0016 := @g_f1ofo D E F
  have p0017 := Nominal.mp hyp_hnordf1oenambndv_2 p0016
  have p0018 := @g_forn D E F
  have p0019 := Nominal.mp p0017 p0018
  have p0020 := @g_rnex F hyp_hnordf1oenambndv_1
  have p0021 := @g_eqeltrri (syn_crn F) E (syn_cvv) p0019 p0020
  have p0022 := @g_hnqincf1 A E hyp_hnordf1oenambndv_4 p0021 hyp_hnordf1oenambndv_5
  have p0023 := @g_f1f1orn (syn_chnord E) (syn_chnord A) (syn_chnqinc E A)
  have p0024 := Nominal.mp p0022 p0023
  have p0031 :=
    @g_pm3_2i (.classMem E (syn_cvv)) (.classMem A (syn_cvv)) p0021 hyp_hnordf1oenambndv_5
  have p0032 := @g_hnqincexg A E
  have p0033 := Nominal.mp p0031 p0032
  have p0034 :=
    @g_f1oen (syn_chnord E) (syn_crn (syn_chnqinc E A)) (syn_chnqinc E A) p0033
  have p0035 := Nominal.mp p0024 p0034
  have p0036 := @g_ensymi (syn_chnord E) (syn_crn (syn_chnqinc E A))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @g_hnqinctrnrneqndv A D E F hyp_hnordf1oenambndv_1 hyp_hnordf1oenambndv_2
      hyp_hnordf1oenambndv_3 hyp_hnordf1oenambndv_4 hyp_hnordf1oenambndv_5
  have p0039 :=
    @g_breq1i (syn_crn (syn_chnqinc D A)) (syn_crn (syn_chnqinc E A)) (syn_chnord E)
      (syn_cen) p0038
  have p0040 :=
    @g_mpbir (syn_wbr (syn_crn (syn_chnqinc D A)) (syn_cen) (syn_chnord E))
      (syn_wbr (syn_crn (syn_chnqinc E A)) (syn_cen) (syn_chnord E)) p0037 p0039
  have p0041 :=
    @g_pm3_2i (syn_wbr (syn_chnord D) (syn_cen) (syn_crn (syn_chnqinc D A)))
      (syn_wbr (syn_crn (syn_chnqinc D A)) (syn_cen) (syn_chnord E)) p0015 p0040
  have p0042 := @g_entr (syn_chnord D) (syn_crn (syn_chnqinc D A)) (syn_chnord E)
  have p0043 := Nominal.mp p0041 p0042
  exact p0043

@[expose]
noncomputable def g_hncardf1oeqambndv (A : Class) (D : Class) (E : Class) (F : Class)
    (hyp_hncardf1oeqambndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hncardf1oeqambndv_2 : Nominal.NPrf (syn_wf1o F D E))
    (hyp_hncardf1oeqambndv_3 : Nominal.NPrf (syn_wss D A))
    (hyp_hncardf1oeqambndv_4 : Nominal.NPrf (syn_wss E A))
    (hyp_hncardf1oeqambndv_5 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_chncard D) (syn_chncard E)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncard D))
  have p0001 :=
    @g_hnordf1oenambndv A D E F hyp_hncardf1oeqambndv_1 hyp_hncardf1oeqambndv_2
      hyp_hncardf1oeqambndv_3 hyp_hncardf1oeqambndv_4 hyp_hncardf1oeqambndv_5
  have p0002 := @g_f1odm D E F
  have p0003 := Nominal.mp hyp_hncardf1oeqambndv_2 p0002
  have p0004 := @g_dmex F hyp_hncardf1oeqambndv_1
  have p0005 := @g_eqeltrri (syn_cdm F) D (syn_cvv) p0003 p0004
  have p0006 := @g_hnordexg D
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_eqnc (syn_chnord D) (syn_chnord E) p0007
  have p0009 :=
    @g_mpbir (.classEq (syn_cnc (syn_chnord D)) (syn_cnc (syn_chnord E)))
      (syn_wbr (syn_chnord D) (syn_cen) (syn_chnord E)) p0001 p0008
  have p0010 :=
    @g_eqtri (syn_chncard D) (syn_cnc (syn_chnord D)) (syn_cnc (syn_chnord E)) p0000 p0009
  have p0011 := (Nominal.classEqRefl (syn_chncard E))
  have p0012 :=
    @g_eqtr4i (syn_chncard D) (syn_cnc (syn_chnord E)) (syn_chncard E) p0010 p0011
  exact p0012

@[expose]
noncomputable def g_hncardf1oeqndv (D : Class) (E : Class) (F : Class)
    (hyp_hncardf1oeqndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_hncardf1oeqndv_2 : Nominal.NPrf (syn_wf1o F D E)) :
    Nominal.NPrf (.classEq (syn_chncard D) (syn_chncard E)) :=
  by
  have p0000 := @g_ssun1 D E
  have p0001 := @g_ssun2 E D
  have p0002 := @g_f1odm D E F
  have p0003 := Nominal.mp hyp_hncardf1oeqndv_2 p0002
  have p0004 := @g_dmex F hyp_hncardf1oeqndv_1
  have p0005 := @g_eqeltrri (syn_cdm F) D (syn_cvv) p0003 p0004
  have p0006 := @g_f1ofo D E F
  have p0007 := Nominal.mp hyp_hncardf1oeqndv_2 p0006
  have p0008 := @g_forn D E F
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_rnex F hyp_hncardf1oeqndv_1
  have p0011 := @g_eqeltrri (syn_crn F) E (syn_cvv) p0009 p0010
  have p0012 := @g_unex D E p0005 p0011
  have p0013 :=
    @g_hncardf1oeqambndv (syn_cun D E) D E F hyp_hncardf1oeqndv_1 hyp_hncardf1oeqndv_2
      p0000 p0001 p0012
  exact p0013

@[expose]
noncomputable def g_hnordeqdndv (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_chnord A) (syn_chnord B))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnord A))
  have p0001 :=
    @g_a1i (.classEq (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)))
      (.classEq A B) p0000
  have p0002 := (Nominal.classEqRefl (syn_chwcn A))
  have p0003 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)))
      (.classEq A B) p0002
  have p0004 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0005 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))))
      (.classEq A B) p0004
  have p0006 := @g_pweq A B
  have p0007 := @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0006
  have p0008 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A))
      (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0007
  have p0009 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A)
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0005 p0008
  have p0010 := (Nominal.classEqRefl (syn_chwcodes B))
  have p0011 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0010
  have p0012 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B))
      (.classEq A B) p0011
  have p0013 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A)
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0009 p0012
  have p0014 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0013
  have p0015 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))
      (syn_cin (syn_chwcodes B) (syn_chwrels)) p0003 p0014
  have p0016 := (Nominal.classEqRefl (syn_chwcn B))
  have p0017 := @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0016
  have p0018 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B))
      (.classEq A B) p0017
  have p0019 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels))
      (syn_chwcn B) p0015 p0018
  have p0020 := @g_qseq1 (syn_chwcn A) (syn_chwcn B) (syn_chwniso A)
  have p0021 :=
    @g_syl (.classEq A B) (.classEq (syn_chwcn A) (syn_chwcn B))
      (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso A)))
      p0019 p0020
  have p0022 := (Nominal.classEqRefl (syn_chwniso A))
  have p0023 :=
    @g_a1i
      (.classEq (syn_chwniso A)
        (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (.classEq A B) p0022
  have p0060 :=
    @g_xpeq12d (.classEq A B) (syn_chwcn A) (syn_chwcn B) (syn_chwcn A) (syn_chwcn B)
      p0019 p0019
  have p0061 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_chwcn A) (syn_chwcn A))
      (syn_cxp (syn_chwcn B) (syn_chwcn B))
      (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) p0060
  have p0062 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn B) (syn_chwcn B)))
      p0023 p0061
  have p0063 := (Nominal.classEqRefl (syn_chwniso B))
  have p0064 :=
    @g_eqcomi (syn_chwniso B)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn B) (syn_chwcn B)))
      p0063
  have p0065 :=
    @g_a1i
      (.classEq (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn B) (syn_chwcn B))) (syn_chwniso B))
      (.classEq A B) p0064
  have p0066 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn B) (syn_chwcn B)))
      (syn_chwniso B) p0062 p0065
  have p0067 := @g_qseq2 (syn_chwniso A) (syn_chwniso B) (syn_chwcn B)
  have p0068 :=
    @g_syl (.classEq A B) (.classEq (syn_chwniso A) (syn_chwniso B))
      (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B)))
      p0066 p0067
  have p0069 :=
    @g_eqtrd (.classEq A B) (syn_cqs (syn_chwcn A) (syn_chwniso A))
      (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B))
      p0021 p0068
  have p0070 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A))
      (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0001 p0069
  have p0071 := (Nominal.classEqRefl (syn_chnord B))
  have p0072 := @g_eqcomi (syn_chnord B) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0071
  have p0073 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso B)) (syn_chnord B))
      (.classEq A B) p0072
  have p0074 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn B) (syn_chwniso B))
      (syn_chnord B) p0070 p0073
  exact p0074

@[expose]
noncomputable def g_hncardeqdndv (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_chncard A) (syn_chncard B))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncard A))
  have p0001 :=
    @g_a1i (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) (.classEq A B) p0000
  have p0002 := (Nominal.classEqRefl (syn_chnord A))
  have p0003 :=
    @g_a1i (.classEq (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)))
      (.classEq A B) p0002
  have p0004 := (Nominal.classEqRefl (syn_chwcn A))
  have p0005 :=
    @g_a1i (.classEq (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)))
      (.classEq A B) p0004
  have p0006 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0007 :=
    @g_a1i (.classEq (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))))
      (.classEq A B) p0006
  have p0008 := @g_pweq A B
  have p0009 := @g_xpeq2d (.classEq A B) (syn_cpw A) (syn_cpw B) (syn_cvv) p0008
  have p0010 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_cvv) (syn_cpw A))
      (syn_cxp (syn_cvv) (syn_cpw B)) (syn_cwe) p0009
  have p0011 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A)
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0007 p0010
  have p0012 := (Nominal.classEqRefl (syn_chwcodes B))
  have p0013 :=
    @g_eqcomi (syn_chwcodes B) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) p0012
  have p0014 :=
    @g_a1i (.classEq (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B))
      (.classEq A B) p0013
  have p0015 :=
    @g_eqtrd (.classEq A B) (syn_chwcodes A)
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw B))) (syn_chwcodes B) p0011 p0014
  have p0016 :=
    @g_ineq1d (.classEq A B) (syn_chwcodes A) (syn_chwcodes B) (syn_chwrels) p0015
  have p0017 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels))
      (syn_cin (syn_chwcodes B) (syn_chwrels)) p0005 p0016
  have p0018 := (Nominal.classEqRefl (syn_chwcn B))
  have p0019 := @g_eqcomi (syn_chwcn B) (syn_cin (syn_chwcodes B) (syn_chwrels)) p0018
  have p0020 :=
    @g_a1i (.classEq (syn_cin (syn_chwcodes B) (syn_chwrels)) (syn_chwcn B))
      (.classEq A B) p0019
  have p0021 :=
    @g_eqtrd (.classEq A B) (syn_chwcn A) (syn_cin (syn_chwcodes B) (syn_chwrels))
      (syn_chwcn B) p0017 p0020
  have p0022 := @g_qseq1 (syn_chwcn A) (syn_chwcn B) (syn_chwniso A)
  have p0023 :=
    @g_syl (.classEq A B) (.classEq (syn_chwcn A) (syn_chwcn B))
      (.classEq (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso A)))
      p0021 p0022
  have p0024 := (Nominal.classEqRefl (syn_chwniso A))
  have p0025 :=
    @g_a1i
      (.classEq (syn_chwniso A)
        (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn A) (syn_chwcn A))))
      (.classEq A B) p0024
  have p0062 :=
    @g_xpeq12d (.classEq A B) (syn_chwcn A) (syn_chwcn B) (syn_chwcn A) (syn_chwcn B)
      p0021 p0021
  have p0063 :=
    @g_ineq2d (.classEq A B) (syn_cxp (syn_chwcn A) (syn_chwcn A))
      (syn_cxp (syn_chwcn B) (syn_chwcn B))
      (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) p0062
  have p0064 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn B) (syn_chwcn B)))
      p0025 p0063
  have p0065 := (Nominal.classEqRefl (syn_chwniso B))
  have p0066 :=
    @g_eqcomi (syn_chwniso B)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn B) (syn_chwcn B)))
      p0065
  have p0067 :=
    @g_a1i
      (.classEq (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn B) (syn_chwcn B))) (syn_chwniso B))
      (.classEq A B) p0066
  have p0068 :=
    @g_eqtrd (.classEq A B) (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn B) (syn_chwcn B)))
      (syn_chwniso B) p0064 p0067
  have p0069 := @g_qseq2 (syn_chwniso A) (syn_chwniso B) (syn_chwcn B)
  have p0070 :=
    @g_syl (.classEq A B) (.classEq (syn_chwniso A) (syn_chwniso B))
      (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B)))
      p0068 p0069
  have p0071 :=
    @g_eqtrd (.classEq A B) (syn_cqs (syn_chwcn A) (syn_chwniso A))
      (syn_cqs (syn_chwcn B) (syn_chwniso A)) (syn_cqs (syn_chwcn B) (syn_chwniso B))
      p0023 p0070
  have p0072 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A))
      (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0003 p0071
  have p0073 := (Nominal.classEqRefl (syn_chnord B))
  have p0074 := @g_eqcomi (syn_chnord B) (syn_cqs (syn_chwcn B) (syn_chwniso B)) p0073
  have p0075 :=
    @g_a1i (.classEq (syn_cqs (syn_chwcn B) (syn_chwniso B)) (syn_chnord B))
      (.classEq A B) p0074
  have p0076 :=
    @g_eqtrd (.classEq A B) (syn_chnord A) (syn_cqs (syn_chwcn B) (syn_chwniso B))
      (syn_chnord B) p0072 p0075
  have p0077 := @g_nceqd (.classEq A B) (syn_chnord A) (syn_chnord B) p0076
  have p0078 :=
    @g_eqtrd (.classEq A B) (syn_chncard A) (syn_cnc (syn_chnord A))
      (syn_cnc (syn_chnord B)) p0001 p0077
  have p0079 := (Nominal.classEqRefl (syn_chncard B))
  have p0080 := @g_eqcomi (syn_chncard B) (syn_cnc (syn_chnord B)) p0079
  have p0081 :=
    @g_a1i (.classEq (syn_cnc (syn_chnord B)) (syn_chncard B)) (.classEq A B) p0080
  have p0082 :=
    @g_eqtrd (.classEq A B) (syn_chncard A) (syn_cnc (syn_chnord B)) (syn_chncard B) p0078
      p0081
  exact p0082

@[expose]
noncomputable def g_hncardf1oimpndv (D : Class) (E : Class) (F : Class)
    (hyp_hncardf1oimpndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wf1o F D E) (.classEq (syn_chncard D) (syn_chncard E))) :=
  by
  have p0000 := @g_iftrue (syn_wf1o F D E) D (syn_c0)
  have p0001 := @g_hncardeqdndv (syn_cif (syn_wf1o F D E) D (syn_c0)) D
  have p0002 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) D)
      (.classEq (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0))) (syn_chncard D)) p0000
      p0001
  have p0003 :=
    @g_eqcomd (syn_wf1o F D E) (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0)))
      (syn_chncard D) p0002
  have p0004 := @g_n_0ex
  have p0005 := @g_ifex (syn_wf1o F D E) F (syn_c0) hyp_hncardf1oimpndv_1 p0004
  have p0006 := @g_id (syn_wf1o F D E)
  have p0007 := @g_iftrue (syn_wf1o F D E) F (syn_c0)
  have p0008 :=
    @g_f1oeq1 (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0))
      (syn_cif (syn_wf1o F D E) F (syn_c0)) F
  have p0009 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) F (syn_c0)) F)
      (syn_wb (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
          (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
        (syn_wf1o F (syn_cif (syn_wf1o F D E) D (syn_c0))
          (syn_cif (syn_wf1o F D E) E (syn_c0))))
      p0007 p0008
  have p0011 :=
    @g_f1oeq2 (syn_cif (syn_wf1o F D E) D (syn_c0)) D
      (syn_cif (syn_wf1o F D E) E (syn_c0)) F
  have p0012 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) D)
      (syn_wb (syn_wf1o F (syn_cif (syn_wf1o F D E) D (syn_c0))
          (syn_cif (syn_wf1o F D E) E (syn_c0)))
        (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))))
      p0000 p0011
  have p0013 :=
    @g_bitrd (syn_wf1o F D E)
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
        (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
      (syn_wf1o F (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
      (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))) p0009 p0012
  have p0014 := @g_iftrue (syn_wf1o F D E) E (syn_c0)
  have p0015 := @g_f1oeq3 (syn_cif (syn_wf1o F D E) E (syn_c0)) E D F
  have p0016 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) E)
      (syn_wb (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D E)) p0014
      p0015
  have p0017 :=
    @g_bitrd (syn_wf1o F D E)
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
        (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
      (syn_wf1o F D (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_wf1o F D E) p0013 p0016
  have p0018 :=
    @g_mpbird (syn_wf1o F D E)
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
        (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
      (syn_wf1o F D E) p0006 p0017
  have p0019 := @g_f1o0
  have p0020 := @g_iffalse (syn_wf1o F D E) F (syn_c0)
  have p0021 := @g_f1oeq1 (syn_c0) (syn_c0) (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0)
  have p0022 :=
    @g_syl (.neg (syn_wf1o F D E))
      (.classEq (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0))
      (syn_wb (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0))
        (syn_wf1o (syn_c0) (syn_c0) (syn_c0)))
      p0020 p0021
  have p0023 :=
    @g_mpbiri (.neg (syn_wf1o F D E))
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0))
      (syn_wf1o (syn_c0) (syn_c0) (syn_c0)) p0019 p0022
  have p0024 := @g_iffalse (syn_wf1o F D E) D (syn_c0)
  have p0025 := @g_iffalse (syn_wf1o F D E) E (syn_c0)
  have p0026 :=
    @g_jca (.neg (syn_wf1o F D E))
      (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_c0))
      (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_c0)) p0024 p0025
  have p0027 :=
    @g_f1oeq23 (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_c0)
      (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_c0) (syn_cif (syn_wf1o F D E) F (syn_c0))
  have p0028 :=
    @g_syl (.neg (syn_wf1o F D E))
      (syn_wa (.classEq (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_c0))
        (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_c0)))
      (syn_wb (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
          (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
        (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0)))
      p0026 p0027
  have p0029 :=
    @g_mpbird (.neg (syn_wf1o F D E))
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
        (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0)) (syn_c0) (syn_c0)) p0023 p0028
  have p0030 :=
    @g_pm2_61i (syn_wf1o F D E)
      (syn_wf1o (syn_cif (syn_wf1o F D E) F (syn_c0))
        (syn_cif (syn_wf1o F D E) D (syn_c0)) (syn_cif (syn_wf1o F D E) E (syn_c0)))
      p0018 p0029
  have p0031 :=
    @g_hncardf1oeqndv (syn_cif (syn_wf1o F D E) D (syn_c0))
      (syn_cif (syn_wf1o F D E) E (syn_c0)) (syn_cif (syn_wf1o F D E) F (syn_c0)) p0005
      p0030
  have p0032 :=
    @g_a1i
      (.classEq (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0)))
        (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))))
      (syn_wf1o F D E) p0031
  have p0033 :=
    @g_eqtrd (syn_wf1o F D E) (syn_chncard D)
      (syn_chncard (syn_cif (syn_wf1o F D E) D (syn_c0)))
      (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))) p0003 p0032
  have p0035 := @g_hncardeqdndv (syn_cif (syn_wf1o F D E) E (syn_c0)) E
  have p0036 :=
    @g_syl (syn_wf1o F D E) (.classEq (syn_cif (syn_wf1o F D E) E (syn_c0)) E)
      (.classEq (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_chncard E)) p0014
      p0035
  have p0037 :=
    @g_eqtrd (syn_wf1o F D E) (syn_chncard D)
      (syn_chncard (syn_cif (syn_wf1o F D E) E (syn_c0))) (syn_chncard E) p0033 p0036
  exact p0037

@[expose]
noncomputable def g_hncardnceqdndv (D : Class) (E : Class)
    (hyp_hncardnceqdndv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (_hyp_hncardnceqdndv_2 : Nominal.NPrf (.classMem E (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classEq (syn_cnc D) (syn_cnc E)) (.classEq (syn_chncard D) (syn_chncard E))) :=
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
  have dv_cache_0003 : f ∉ ((Wff.classEq (syn_chncard D) (syn_chncard E))).fv :=
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
  have p0000 := @g_eqnc D E hyp_hncardnceqdndv_1
  have p0001 := @g_biimpi (.classEq (syn_cnc D) (syn_cnc E)) (syn_wbr D (syn_cen) E) p0000
  have p0002 := @g_bren D E f dv_cache_0001 dv_cache_0002
  have p0003 := @g_biimpi (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0002
  have p0004 :=
    @g_syl (.classEq (syn_cnc D) (syn_cnc E)) (syn_wbr D (syn_cen) E)
      (syn_wex f (syn_wf1o (.cv f) D E)) p0001 p0003
  have p0005 := @g_vex f
  have p0006 := @g_hncardf1oimpndv D E (.cv f) p0005
  have p0007 :=
    @g_exlimiv (syn_wf1o (.cv f) D E) (.classEq (syn_chncard D) (syn_chncard E)) f
      dv_cache_0003 p0006
  have p0008 :=
    @g_syl (.classEq (syn_cnc D) (syn_cnc E)) (syn_wex f (syn_wf1o (.cv f) D E))
      (.classEq (syn_chncard D) (syn_chncard E)) p0004 p0007
  exact p0008

@[expose]
noncomputable def g_hncardnceqndv (D : Class) (E : Class)
    (hyp_hncardnceqndv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hncardnceqndv_2 : Nominal.NPrf (.classMem E (syn_cvv)))
    (hyp_hncardnceqndv_3 : Nominal.NPrf (.classEq (syn_cnc D) (syn_cnc E))) :
    Nominal.NPrf (.classEq (syn_chncard D) (syn_chncard E)) :=
  by
  have p0000 := @g_hncardnceqdndv D E hyp_hncardnceqndv_1 hyp_hncardnceqndv_2
  have p0001 := Nominal.mp hyp_hncardnceqndv_3 p0000
  exact p0001

@[expose]
noncomputable def g_wppcardt4fnexndv :
    Nominal.NPrf (.classMem (syn_cwppcardt4fn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardt4fn))
  have p0001 := @g_wppcardt2fnexndv
  have p0003 := @g_siex (syn_cwppcardt2fn) p0001
  have p0004 := @g_siex (syn_csi (syn_cwppcardt2fn)) p0003
  have p0005 :=
    @g_coex (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))) p0001 p0004
  have p0006 :=
    @g_eqeltri (syn_cwppcardt4fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) (syn_cvv) p0000
      p0005
  exact p0006

@[expose]
noncomputable def g_wppcardt4fnmapndv :
    Nominal.NPrf
      (syn_wf (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
        (syn_cncs)) :=
  by
  have p0000 := @g_wppcardt2fnmapndv
  have p0002 := @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
  have p0003 := Nominal.mp p0000 p0002
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs))
      (syn_csi (syn_cwppcardt2fn))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0000 p0005
  have p0007 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt2fn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (syn_cwppcardt4fn))
  have p0010 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) p0009
  have p0011 :=
    @g_mpbir
      (syn_wf (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
        (syn_cncs))
      (syn_wf (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs))
      p0008 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end
