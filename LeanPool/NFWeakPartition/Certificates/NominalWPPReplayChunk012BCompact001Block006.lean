/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012BCompact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_otsnelsi3 (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_otsnelsi3_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_otsnelsi3_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_otsnelsi3_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_csi3 R))
        (.classMem (syn_cop A (syn_cop B C)) R)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have dv_cache_0001 : p ∉ ((syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, fresh_p_not_C, or_false, not_false_eq_true])
  have dv_cache_0002 :
    p ∉
      ((syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
            (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_c1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_c2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cproj2 (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_p,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, fresh_x_not_B, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, fresh_x_not_C, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_cop A (syn_cop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, fresh_p_not_C, or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_csi3 R))
  have p0001 :=
    @g_eleq2i (syn_csi3 R)
      (syn_cima (syn_ctxp (syn_csi (syn_c1st))
          (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
            (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 R))
      (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) p0000
  have p0002 :=
    @g_elimapw1 p (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C)))
      (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
          (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))
      R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_oteltxp (syn_csn (.cv p)) (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))
      (syn_csi (syn_c1st))
      (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
        (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))
  have p0004 := @g_vex p
  have p0005 := @g_opsnelsi (.cv p) A (syn_c1st) p0004 hyp_otsnelsi3_1
  have p0006 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) A))
  have p0007 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn A)) (syn_csi (syn_c1st)))
      (.classMem (syn_cop (.cv p) A) (syn_c1st)) (syn_wbr (.cv p) (syn_c1st) A) p0005
      p0006
  have p0008 :=
    @g_oteltxp (syn_csn (.cv p)) (syn_csn B) (syn_csn C)
      (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
      (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))
  have p0009 :=
    @g_opsnelsi (.cv p) B (syn_ccom (syn_c1st) (syn_c2nd)) p0004 hyp_otsnelsi3_2
  have p0010 :=
    @g_opelco x (.cv p) B (syn_c1st) (syn_c2nd) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0011 := @g_opeq (.cv p)
  have p0012 :=
    @g_breq1i (.cv p) (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (.cv x)
      (syn_c2nd) p0011
  have p0013 := @g_proj1ex (.cv p) p0004
  have p0014 := @g_proj2ex (.cv p) p0004
  have p0015 := @g_opbr2nd (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p)) (.cv x) p0013 p0014
  have p0016 := @g_eqcom (syn_cproj2 (.cv p)) (.cv x)
  have p0017 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_c2nd) (.cv x))
      (syn_wbr (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (syn_c2nd) (.cv x))
      (.classEq (syn_cproj2 (.cv p)) (.cv x)) (.classEq (.cv x) (syn_cproj2 (.cv p)))
      p0012 p0015 p0016
  have p0018 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (.classEq (.cv x) (syn_cproj2 (.cv p)))
      (syn_wbr (.cv x) (syn_c1st) B) p0017
  have p0019 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c1st) B))
      (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c1st) B)) x
      p0018
  have p0020 := @g_breq1 (.cv x) (syn_cproj2 (.cv p)) B (syn_c1st)
  have p0021 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_c1st) B) (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B)
      x (syn_cproj2 (.cv p)) dv_cache_0008 dv_cache_0009 p0014 p0020
  have p0022 :=
    @g_bitri
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c1st) B)))
      (syn_wex x
        (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c1st) B)))
      (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) p0019 p0021
  have p0023 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn B))
        (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))))
      (.classMem (syn_cop (.cv p) B) (syn_ccom (syn_c1st) (syn_c2nd)))
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c1st) B)))
      (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B) p0009 p0010 p0022
  have p0024 :=
    @g_opsnelsi (.cv p) C (syn_ccom (syn_c2nd) (syn_c2nd)) p0004 hyp_otsnelsi3_3
  have p0025 :=
    @g_opelco x (.cv p) C (syn_c2nd) (syn_c2nd) dv_cache_0004 dv_cache_0010 dv_cache_0007
      dv_cache_0007
  have p0026 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (.classEq (.cv x) (syn_cproj2 (.cv p)))
      (syn_wbr (.cv x) (syn_c2nd) C) p0017
  have p0027 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) C))
      (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c2nd) C)) x
      p0026
  have p0028 := @g_breq1 (.cv x) (syn_cproj2 (.cv p)) C (syn_c2nd)
  have p0029 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_c2nd) C) (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C)
      x (syn_cproj2 (.cv p)) dv_cache_0008 dv_cache_0011 p0014 p0028
  have p0030 :=
    @g_bitri
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) C)))
      (syn_wex x
        (syn_wa (.classEq (.cv x) (syn_cproj2 (.cv p))) (syn_wbr (.cv x) (syn_c2nd) C)))
      (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) p0027 p0029
  have p0031 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn C))
        (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))
      (.classMem (syn_cop (.cv p) C) (syn_ccom (syn_c2nd) (syn_c2nd)))
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) C)))
      (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) p0024 p0025 p0030
  have p0032 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn B))
        (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))))
      (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B)
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn C))
        (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))
      (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C) p0023 p0031
  have p0033 :=
    @g_opbr2nd (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p)) (syn_cop B C) p0013 p0014
  have p0034 :=
    @g_breq1i (.cv p) (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (syn_cop B C)
      (syn_c2nd) p0011
  have p0035 := @g_op1st2nd B C (syn_cproj2 (.cv p)) hyp_otsnelsi3_2 hyp_otsnelsi3_3
  have p0036 :=
    @g_n_3bitr4ri
      (syn_wbr (syn_cop (syn_cproj1 (.cv p)) (syn_cproj2 (.cv p))) (syn_c2nd) (syn_cop B C))
      (.classEq (syn_cproj2 (.cv p)) (syn_cop B C))
      (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C))
      (syn_wa (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B)
        (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C))
      p0033 p0034 p0035
  have p0037 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn B) (syn_csn C)))
        (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
          (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn B))
          (syn_csi (syn_ccom (syn_c1st) (syn_c2nd))))
        (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn C))
          (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))
      (syn_wa (syn_wbr (syn_cproj2 (.cv p)) (syn_c1st) B)
        (syn_wbr (syn_cproj2 (.cv p)) (syn_c2nd) C))
      (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C)) p0008 p0032 p0036
  have p0038 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn A)) (syn_csi (syn_c1st)))
      (syn_wbr (.cv p) (syn_c1st) A)
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn B) (syn_csn C)))
        (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
          (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))
      (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C)) p0007 p0037
  have p0039 := @g_opex B C hyp_otsnelsi3_2 hyp_otsnelsi3_3
  have p0040 := @g_op1st2nd A (syn_cop B C) (.cv p) hyp_otsnelsi3_1 p0039
  have p0041 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))))
        (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
            (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn A)) (syn_csi (syn_c1st)))
        (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn B) (syn_csn C)))
          (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
            (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) A) (syn_wbr (.cv p) (syn_c2nd) (syn_cop B C)))
      (.classEq (.cv p) (syn_cop A (syn_cop B C))) p0003 p0038 p0040
  have p0042 :=
    @g_rexbii
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))))
        (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
            (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))))
      (.classEq (.cv p) (syn_cop A (syn_cop B C))) p R p0041
  have p0043 := @g_risset p (syn_cop A (syn_cop B C)) R dv_cache_0012 dv_cache_0003
  have p0044 :=
    @g_bitr4i
      (syn_wrex p R (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))))
          (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
              (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))))
      (syn_wrex p R (.classEq (.cv p) (syn_cop A (syn_cop B C))))
      (.classMem (syn_cop A (syn_cop B C)) R) p0042 p0043
  have p0045 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_csi3 R))
      (.classMem (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))) (syn_cima
          (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
              (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 R)))
      (syn_wrex p R (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn A) (syn_cop (syn_csn B) (syn_csn C))))
          (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
              (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))))
      (.classMem (syn_cop A (syn_cop B C)) R) p0001 p0002 p0044
  exact p0045

@[expose]
noncomputable def g_si3ex (A : Class)
    (hyp_si3ex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csi3 A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_csi3 A))
  have p0001 := @g_n_1stex
  have p0002 := @g_siex (syn_c1st) p0001
  have p0004 := @g_n_2ndex
  have p0005 := @g_coex (syn_c1st) (syn_c2nd) p0001 p0004
  have p0006 := @g_siex (syn_ccom (syn_c1st) (syn_c2nd)) p0005
  have p0009 := @g_coex (syn_c2nd) (syn_c2nd) p0004 p0004
  have p0010 := @g_siex (syn_ccom (syn_c2nd) (syn_c2nd)) p0009
  have p0011 :=
    @g_txpex (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
      (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))) p0006 p0010
  have p0012 :=
    @g_txpex (syn_csi (syn_c1st))
      (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
        (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))
      p0002 p0011
  have p0013 := @g_pw1ex A hyp_si3ex_1
  have p0014 :=
    @g_imaex
      (syn_ctxp (syn_csi (syn_c1st)) (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
          (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd)))))
      (syn_cpw1 A) p0012 p0013
  have p0015 :=
    @g_eqeltri (syn_csi3 A)
      (syn_cima (syn_ctxp (syn_csi (syn_c1st))
          (syn_ctxp (syn_csi (syn_ccom (syn_c1st) (syn_c2nd)))
            (syn_csi (syn_ccom (syn_c2nd) (syn_c2nd))))) (syn_cpw1 A))
      (syn_cvv) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_releqel (x : Var) (y : Var) (A : Class) (R : Class) (T : Class)
    (dv_A_y : y ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_T_y : y ∉ T.fv) (dv_x_y : x ≠ y)
    (hyp_releqel_1 : Nominal.NPrf (.classMem T (syn_cvv)))
    (hyp_releqel_2 : Nominal.NPrf
        (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) T) R) (.classMem (.cv y) A))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) T) (syn_ccompl
            (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
        (.classEq (.cv x) A)) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cop (.cv x) T)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_T_y, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          dv_R_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
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
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have p0000 :=
    @g_elima1c y (syn_cop (.cv x) T) (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elsymdif (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset))
      (syn_cins2 R)
  have p0002 := @g_otelins3 (syn_csn (.cv y)) (.cv x) T (syn_csset) hyp_releqel_1
  have p0003 := @g_vex y
  have p0004 := @g_vex x
  have p0005 := @g_opelssetsn (.cv y) (.cv x) p0003 p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x) p0002
      p0006_e01_recanon
  have p0007 := @g_otelins2 (syn_csn (.cv y)) (.cv x) T R p0004
  have p0008 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins2 R))
      (.classMem (syn_cop (syn_csn (.cv y)) T) R) (.classMem (.cv y) A) p0007
      hyp_releqel_2
  have p0009 :=
    @g_bibi12i
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins3 (syn_csset)))
      (.objMem y x)
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins2 R))
      (.classMem (.cv y) A) p0006 p0008
  have p0010 :=
    @g_xchbinx
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T))
        (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)))
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T))
          (syn_cins3 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T)) (syn_cins2 R)))
      (syn_wb (.objMem y x) (.classMem (.cv y) A)) p0001 p0009
  have p0011 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T))
        (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)))
      (.neg (syn_wb (.objMem y x) (.classMem (.cv y) A))) y p0010
  have p0012 := @g_exnal (syn_wb (.objMem y x) (.classMem (.cv y) A)) y
  have p0013 :=
    @g_n_3bitrri
      (.classMem (syn_cop (.cv x) T)
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) T))
          (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R))))
      (syn_wex y (.neg (syn_wb (.objMem y x) (.classMem (.cv y) A))))
      (.neg (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A)))) p0000 p0011 p0012
  have p0014 :=
    @g_con1bii (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A)))
      (.classMem (syn_cop (.cv x) T)
        (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))
      p0013
  have p0015 := @g_opex (.cv x) T p0004 hyp_releqel_1
  have p0016 :=
    @g_elcompl (syn_cop (.cv x) T)
      (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)) p0015
  have p0017 := @g_dfcleq y (.cv x) A dv_cache_0003 dv_cache_0004
  have p0018_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv x) A) (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_cop (.cv x) T)
          (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
      (.all y (syn_wb (.objMem y x) (.classMem (.cv y) A)))
      (.classMem (syn_cop (.cv x) T) (syn_ccompl
          (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
      (.classEq (.cv x) A) p0014 p0016 p0018_e02_recanon
  exact p0018

@[expose]
noncomputable def g_releqmpt (x : Var) (y : Var) (A : Class) (R : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_V_y : y ∉ V.fv)
    (dv_x_y : x ≠ y)
    (hyp_releqmpt_1 : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) R)
          (.classMem (.cv y) V))) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))
        (syn_cmpt x A V)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (V).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_V_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
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
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0004 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0005 :
    x ∉
      ((syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, dv_A_x,
          dv_R_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_R, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 : z ∉ (V).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_V, not_false_eq_true])
  have p0000 :=
    @g_elin (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv))
      (syn_ccnv (syn_ccompl
          (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
  have p0001 := @g_vex z
  have p0002 := @g_opelxp (.cv x) (.cv z) A (syn_cvv)
  have p0003 :=
    @g_mpbiran2 (.classMem (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv)))
      (.classMem (.cv x) A) (.classMem (.cv z) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_opelcnv (.cv x) (.cv z)
      (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))
  have p0005 := @g_vex x
  have p0006 :=
    @g_releqel z y V R (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      p0005 hyp_releqmpt_1
  have p0007 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (.cv z)) (syn_ccnv (syn_ccompl
            (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))
      (.classMem (syn_cop (.cv z) (.cv x)) (syn_ccompl
          (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
      (.classEq (.cv z) V) p0004 p0006
  have p0008 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv)))
      (.classMem (.cv x) A)
      (.classMem (syn_cop (.cv x) (.cv z)) (syn_ccnv (syn_ccompl
            (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))
      (.classEq (.cv z) V) p0003 p0007
  have p0009 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (.cv z)) (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (syn_cxp A (syn_cvv)))
        (.classMem (syn_cop (.cv x) (.cv z)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))))
      (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) V)) p0000 p0008
  have p0010 :=
    @g_opabbi2i (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) V)) x z
      (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
            (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x z A V
      dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0012 :=
    @g_eqtr4i
      (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
            (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))
      (syn_copab x z (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) V))) (syn_cmpt x A V)
      p0010 p0011
  exact p0012

@[expose]
noncomputable def g_releqmpt2 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (R : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_V_z : z ∉ V.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_releqmpt2_1 : Nominal.NPrf
        (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) R)
          (.classMem (.cv z) V))) :
    Nominal.NPrf
      (.classEq (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))
        (syn_cmpt2 x A y B V)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ B.fv ∪
        R.fv ∪
      V.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0002 : z ∉ (V).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_V_z, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))).fv :=
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
          Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_y_z), fresh_z_ne_w,
          or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          dv_R_z, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, dv_A_x,
          dv_B_x, dv_R_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉
      ((syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, dv_A_y,
          dv_B_y, dv_R_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    w ∉
      ((syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_w_not_A, fresh_w_not_B, fresh_w_not_R, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0010 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0011 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0012 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0013 : w ∉ (V).fv :=
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
        simp only [fresh_w_not_V, not_false_eq_true])
  have p0000 :=
    @g_eldif (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv))
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))
  have p0001 := @g_vex w
  have p0002 := @g_opelxp (syn_cop (.cv x) (.cv y)) (.cv w) (syn_cxp A B) (syn_cvv)
  have p0003 :=
    @g_mpbiran2
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B)) (.classMem (.cv w) (syn_cvv))
      p0001 p0002
  have p0004 := @g_opelxp (.cv x) (.cv y) A B
  have p0005 :=
    @g_bitri
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0003 p0004
  have p0006 := @g_dfcleq z (.cv w) V dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_elima1c z (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
      (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_elsymdif (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
      (syn_cins2 (syn_csset)) (syn_cins3 R)
  have p0009 := @g_vex x
  have p0010 := @g_vex y
  have p0011 := @g_opex (.cv x) (.cv y) p0009 p0010
  have p0012 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (.cv w) (syn_csset) p0011
  have p0013 := @g_vex z
  have p0014 := @g_opelssetsn (.cv z) (.cv w) p0013 p0001
  have p0015_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv w)) (syn_csset)) (.objMem z w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0015 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv w)) (syn_csset)) (.objMem z w) p0012
      p0015_e01_recanon
  have p0016 := @g_otelins3 (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (.cv w) R p0001
  have p0017 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
        (syn_cins3 R))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) R)
      (.classMem (.cv z) V) p0016 hyp_releqmpt2_1
  have p0018 :=
    @g_bibi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
        (syn_cins2 (syn_csset)))
      (.objMem z w)
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
        (syn_cins3 R))
      (.classMem (.cv z) V) p0015 p0017
  have p0019 :=
    @g_xchbinx
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
        (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)))
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
          (syn_cins2 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
          (syn_cins3 R)))
      (syn_wb (.objMem z w) (.classMem (.cv z) V)) p0008 p0018
  have p0020 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
        (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)))
      (.neg (syn_wb (.objMem z w) (.classMem (.cv z) V))) z p0019
  have p0021 := @g_exnal (syn_wb (.objMem z w) (.classMem (.cv z) V)) z
  have p0022 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))
      (syn_wex z
        (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R))))
      (syn_wex z (.neg (syn_wb (.objMem z w) (.classMem (.cv z) V))))
      (.neg (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V)))) p0007 p0020 p0021
  have p0023 :=
    @g_con2bii
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))
      (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V))) p0022
  have p0024_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv w) V) (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0024 :=
    @g_bitr2i (.classEq (.cv w) V) (.all z (syn_wb (.objMem z w) (.classMem (.cv z) V)))
      (.neg (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))))
      p0024_e00_recanon p0023
  have p0025 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) (syn_cxp (syn_cxp A B) (syn_cvv)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (.neg (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))))
      (.classEq (.cv w) V) p0005 p0024
  have p0026 :=
    @g_bitri
      (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
        (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
          (syn_cxp (syn_cxp A B) (syn_cvv))) (.neg
          (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
            (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V))
      p0000 p0025
  have p0027 :=
    @g_oprabbi2i
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V)) x
      y w
      (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0026
  have p0028 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 x y w A B V
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0009 dv_cache_0010
  have p0029 :=
    @g_eqtr4i
      (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))
      (syn_coprab x y w (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv w) V)))
      (syn_cmpt2 x A y B V) p0027 p0028
  exact p0029

@[expose]
noncomputable def g_mptexlem (A : Class) (R : Class)
    (hyp_mptexlem_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_mptexlem_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cin (syn_cxp A (syn_cvv)) (syn_ccnv (syn_ccompl
              (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))))
        (syn_cvv)) :=
  by
  have p0000 := @g_vvex
  have p0001 := @g_xpex A (syn_cvv) hyp_mptexlem_1 p0000
  have p0002 := @g_ssetex
  have p0003 := @g_ins3ex (syn_csset) p0002
  have p0004 := @g_ins2ex R hyp_mptexlem_2
  have p0005 := @g_symdifex (syn_cins3 (syn_csset)) (syn_cins2 R) p0003 p0004
  have p0006 := @g_n_1cex
  have p0007 :=
    @g_imaex (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c) p0005 p0006
  have p0008 :=
    @g_complex (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))
      p0007
  have p0009 :=
    @g_cnvex
      (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c)))
      p0008
  have p0010 :=
    @g_inex (syn_cxp A (syn_cvv))
      (syn_ccnv (syn_ccompl
          (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 R)) (syn_c1c))))
      p0001 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_mpt2exlem (A : Class) (B : Class) (R : Class)
    (hyp_mpt2exlem_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_mpt2exlem_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_mpt2exlem_3 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cdif (syn_cxp (syn_cxp A B) (syn_cvv))
          (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)))
        (syn_cvv)) :=
  by
  have p0000 := @g_xpex A B hyp_mpt2exlem_1 hyp_mpt2exlem_2
  have p0001 := @g_vvex
  have p0002 := @g_xpex (syn_cxp A B) (syn_cvv) p0000 p0001
  have p0003 := @g_ssetex
  have p0004 := @g_ins2ex (syn_csset) p0003
  have p0005 := @g_ins3ex R hyp_mpt2exlem_3
  have p0006 := @g_symdifex (syn_cins2 (syn_csset)) (syn_cins3 R) p0004 p0005
  have p0007 := @g_n_1cex
  have p0008 :=
    @g_imaex (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c) p0006 p0007
  have p0009 :=
    @g_difex (syn_cxp (syn_cxp A B) (syn_cvv))
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 R)) (syn_c1c)) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_cupvalg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (.classEq (syn_co A (syn_ccup) B) (syn_cun A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cun A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_elex A V
  have p0001 := @g_elex B W
  have p0002 := @g_unexg A B (syn_cvv) (syn_cvv)
  have p0003 := @g_uneq1 (.cv x) A (.cv y)
  have p0004 := @g_uneq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cup x y
      dv_cache_0001
  have p0006 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (syn_cun (.cv x) (.cv y)) (syn_cun A B)
      (syn_ccup) (syn_cun A (.cv y)) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @g_mpd3an3 (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cun A B) (syn_cvv)) (.classEq (syn_co A (syn_ccup) B) (syn_cun A B))
      p0002 p0006
  have p0008 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classEq (syn_co A (syn_ccup) B) (syn_cun A B)) (.classMem B W) p0000 p0001 p0007
  exact p0008

@[expose]
noncomputable def g_fncup : Nominal.NPrf (syn_wfn (syn_ccup) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cup x y
      dv_cache_0001
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_unex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_fnmpt2i x y (syn_cvv) (syn_cvv) (syn_cun (.cv x) (.cv y)) (syn_ccup) dv_cache_0002
      dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @g_xpvv
  have p0006 := @g_fneq2i (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ccup) p0005
  have p0007 :=
    @g_mpbi (syn_wfn (syn_ccup) (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ccup) (syn_cvv)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_brcupg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (syn_wbr (syn_cop A B) (syn_ccup) C) (.classEq C (syn_cun A B)))) :=
  by
  have p0000 := @g_fncup
  have p0001 := @g_opexg A B V W
  have p0002 := @g_fnbrfvb (syn_cvv) (syn_cop A B) C (syn_ccup)
  have p0003 :=
    @g_sylancr (syn_wa (.classMem A V) (.classMem B W)) (syn_wfn (syn_ccup) (syn_cvv))
      (.classMem (syn_cop A B) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_ccup) (syn_cop A B)) C)
        (syn_wbr (syn_cop A B) (syn_ccup) C))
      p0000 p0001 p0002
  have p0004 := @g_cupvalg A B V W
  have p0005 :=
    @g_eqeq1d (syn_wa (.classMem A V) (.classMem B W)) (syn_co A (syn_ccup) B)
      (syn_cun A B) C p0004
  have p0006 := (Nominal.classEqRefl (syn_co A (syn_ccup) B))
  have p0007 :=
    @g_eqeq1i (syn_co A (syn_ccup) B) (syn_cfv (syn_ccup) (syn_cop A B)) C p0006
  have p0008 := @g_eqcom (syn_cun A B) C
  have p0009 :=
    @g_n_3bitr3g (syn_wa (.classMem A V) (.classMem B W))
      (.classEq (syn_co A (syn_ccup) B) C) (.classEq (syn_cun A B) C)
      (.classEq (syn_cfv (syn_ccup) (syn_cop A B)) C) (.classEq C (syn_cun A B)) p0005
      p0007 p0008
  have p0010 :=
    @g_bitr3d (syn_wa (.classMem A V) (.classMem B W))
      (.classEq (syn_cfv (syn_ccup) (syn_cop A B)) C) (syn_wbr (syn_cop A B) (syn_ccup) C)
      (.classEq C (syn_cun A B)) p0003 p0009
  exact p0010

@[expose]
noncomputable def g_brcup (A : Class) (B : Class) (C : Class)
    (hyp_brcup_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brcup_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop A B) (syn_ccup) C) (.classEq C (syn_cun A B))) :=
  by
  have p0000 := @g_brcupg A B C (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr (syn_cop A B) (syn_ccup) C) (.classEq C (syn_cun A B))) hyp_brcup_1
      hyp_brcup_2 p0000
  exact p0001

@[expose]
noncomputable def g_cupex : Nominal.NPrf (.classMem (syn_ccup) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    y ∉ ((syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉ ((syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cun (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cup x y
      dv_cache_0001
  have p0001 := @g_vex y
  have p0002 := @g_otelins3 (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) p0001
  have p0003 := @g_vex z
  have p0004 := @g_vex x
  have p0005 := @g_opelssetsn (.cv z) (.cv x) p0003 p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0002
      p0006_e01_recanon
  have p0007 := @g_otelins2 (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) p0004
  have p0008 := @g_opelssetsn (.cv z) (.cv y) p0003 p0001
  have p0009_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y) p0007
      p0009_e01_recanon
  have p0010 :=
    @g_orbi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)))
      (.objMem z x)
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.objMem z y) p0006 p0009
  have p0011 :=
    @g_elun (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))
      (syn_cins2 (syn_csset))
  have p0012 := @g_elun (.cv z) (.cv x) (.cv y)
  have p0013_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cun (.cv x) (.cv y)))
        (syn_wo (.objMem z x) (.objMem z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wo
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @g_n_3bitr4i
      (syn_wo (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
          (syn_cins3 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
          (syn_cins2 (syn_csset))))
      (syn_wo (.objMem z x) (.objMem z y))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
        (syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))
      (.classMem (.cv z) (syn_cun (.cv x) (.cv y))) p0010 p0011 p0013_e02_recanon
  have p0014 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv)
      (syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))) (syn_cun (.cv x) (.cv y))
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 p0013
  have p0015 :=
    @g_eqtr4i (syn_ccup) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cun (.cv x) (.cv y)))
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))) (syn_c1c)))
      p0000 p0014
  have p0016 := @g_vvex
  have p0018 := @g_ssetex
  have p0019 := @g_ins3ex (syn_csset) p0018
  have p0021 := @g_ins2ex (syn_csset) p0018
  have p0022 := @g_unex (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)) p0019 p0021
  have p0023 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv)
      (syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))) p0016 p0016 p0022
  have p0024 :=
    @g_eqeltri (syn_ccup)
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset))
            (syn_cins3 (syn_cun (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))) (syn_c1c)))
      (syn_cvv) p0015 p0023
  exact p0024

@[expose]
noncomputable def g_composevalg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (.classEq (syn_co A (syn_ccompose) B) (syn_ccom A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_ccom A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_ccom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_ccom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_elex A V
  have p0001 := @g_adantr (.classMem A V) (.classMem A (syn_cvv)) (.classMem B W) p0000
  have p0002 := @g_elex B W
  have p0003 := @g_adantl (.classMem B W) (.classMem B (syn_cvv)) (.classMem A V) p0002
  have p0004 := @g_coexg A B V W
  have p0005 := @g_coeq1 (.cv x) A (.cv y)
  have p0006 := @g_coeq2 (.cv y) B A
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_compose x y
      dv_cache_0001
  have p0008 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (syn_ccom (.cv x) (.cv y)) (syn_ccom A B)
      (syn_ccompose) (syn_ccom A (.cv y)) (syn_cvv) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0001 p0005 p0006 p0007
  have p0009 :=
    @g_syl3anc (syn_wa (.classMem A V) (.classMem B W)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv)) (.classMem (syn_ccom A B) (syn_cvv))
      (.classEq (syn_co A (syn_ccompose) B) (syn_ccom A B)) p0001 p0003 p0004 p0008
  exact p0009

@[expose]
noncomputable def g_composefn : Nominal.NPrf (syn_wfn (syn_ccompose) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have dv_cache_0001 : z ∉ ((syn_ccom (.cv x) (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0006 : z ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_vex x
  have p0001 := @g_vex y
  have p0002 := @g_coex (.cv x) (.cv y) p0000 p0001
  have p0003 := @g_eueq1 z (syn_ccom (.cv x) (.cv y)) dv_cache_0001 p0002
  have p0004 :=
    @g_a1i (syn_weu z (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) p0003
  have p0005 :=
    @g_fnoprab (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
      (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))) x y z dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_compose x y
      dv_cache_0003
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 x y z (syn_cvv)
      (syn_cvv) (syn_ccom (.cv x) (.cv y)) dv_cache_0006 dv_cache_0006 dv_cache_0001
      dv_cache_0004 dv_cache_0005
  have p0008 :=
    @g_eqtri (syn_ccompose) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_ccom (.cv x) (.cv y)))
      (syn_coprab x y z
        (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
          (.classEq (.cv z) (syn_ccom (.cv x) (.cv y)))))
      p0006 p0007
  have p0009 := @g_xpvv
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y (syn_cvv)
      (syn_cvv) dv_cache_0007 dv_cache_0008 dv_cache_0007 dv_cache_0008 dv_cache_0003
  have p0011 :=
    @g_eqtr3i (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      p0009 p0010
  have p0012 :=
    @g_fneq1 (syn_cvv) (syn_ccompose)
      (syn_coprab x y z
        (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
          (.classEq (.cv z) (syn_ccom (.cv x) (.cv y)))))
  have p0013 :=
    @g_fneq2 (syn_cvv)
      (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      (syn_coprab x y z
        (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
          (.classEq (.cv z) (syn_ccom (.cv x) (.cv y)))))
  have p0014 :=
    @g_sylan9bb
      (.classEq (syn_ccompose) (syn_coprab x y z
          (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
            (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))))
      (syn_wfn (syn_ccompose) (syn_cvv))
      (syn_wfn (syn_coprab x y z
          (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
            (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))) (syn_cvv))
      (.classEq (syn_cvv) (syn_copab x y
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (syn_wfn (syn_coprab x y z
          (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
            (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))) (syn_copab x y
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      p0012 p0013
  have p0015 :=
    @g_mp2an
      (.classEq (syn_ccompose) (syn_coprab x y z
          (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
            (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))))
      (.classEq (syn_cvv) (syn_copab x y
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      (syn_wb (syn_wfn (syn_ccompose) (syn_cvv)) (syn_wfn (syn_coprab x y z
            (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
              (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))) (syn_copab x y
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      p0008 p0011 p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_ccompose) (syn_cvv))
      (syn_wfn (syn_coprab x y z
          (syn_wa (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
            (.classEq (.cv z) (syn_ccom (.cv x) (.cv y))))) (syn_copab x y
          (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))
      p0005 p0015
  exact p0016

@[expose]
noncomputable def g_brcomposeg (A : Class) (B : Class) (C : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (syn_wbr (syn_cop A B) (syn_ccompose) C) (.classEq (syn_ccom A B) C))) :=
  by
  have p0000 := @g_composefn
  have p0001 := @g_opexg A B V W
  have p0002 := @g_fnbrfvb (syn_cvv) (syn_cop A B) C (syn_ccompose)
  have p0003 :=
    @g_sylancr (syn_wa (.classMem A V) (.classMem B W)) (syn_wfn (syn_ccompose) (syn_cvv))
      (.classMem (syn_cop A B) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_ccompose) (syn_cop A B)) C)
        (syn_wbr (syn_cop A B) (syn_ccompose) C))
      p0000 p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_co A (syn_ccompose) B))
  have p0005 := @g_composevalg A B V W
  have p0006 :=
    @g_syl5eqr (syn_wa (.classMem A V) (.classMem B W))
      (syn_cfv (syn_ccompose) (syn_cop A B)) (syn_co A (syn_ccompose) B) (syn_ccom A B)
      p0004 p0005
  have p0007 :=
    @g_eqeq1d (syn_wa (.classMem A V) (.classMem B W))
      (syn_cfv (syn_ccompose) (syn_cop A B)) (syn_ccom A B) C p0006
  have p0008 :=
    @g_bitr3d (syn_wa (.classMem A V) (.classMem B W))
      (.classEq (syn_cfv (syn_ccompose) (syn_cop A B)) C)
      (syn_wbr (syn_cop A B) (syn_ccompose) C) (.classEq (syn_ccom A B) C) p0003 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_composeex : Nominal.NPrf (.classMem (syn_ccompose) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let u : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  let v : Var := freshVar proofSupport 6
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
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
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_t_ne_v : t ≠ v :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_v_ne_t : v ≠ t := Ne.symm fresh_t_ne_v
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_z, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_y, not_false_eq_true])
  have dv_cache_0009 : u ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_y, not_false_eq_true])
  have dv_cache_0010 : w ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0011 : w ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0012 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0013 : w ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    w ∉
      ((syn_cima (syn_cin (syn_cins4 (syn_csi3
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                  (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    t ∉
      ((syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y,
          or_false, not_false_eq_true])
  have dv_cache_0016 :
    t ∉
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                (syn_c1c))) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    u ∉
      ((syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_t, fresh_u_ne_w, fresh_u_ne_z, fresh_u_ne_x,
          fresh_u_ne_y, or_false, not_false_eq_true])
  have dv_cache_0018 :
    u ∉
      ((syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
            (syn_c1c)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((syn_cop (.cv w) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_u, or_false, not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_u, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_x,
          fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0021 :
    t ∉
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : v ∉ ((syn_cop (.cv u) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_t, or_false, not_false_eq_true])
  have dv_cache_0023 : v ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_x, not_false_eq_true])
  have dv_cache_0024 :
    v ∉
      ((syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
              (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_t, fresh_v_ne_w, fresh_v_ne_z,
          fresh_v_ne_x, fresh_v_ne_y, or_false, not_false_eq_true])
  have dv_cache_0025 :
    v ∉
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0027 : y ∉ ((syn_cvv)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0028 :
    x ∉
      ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3
                  (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                    (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                  (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                    (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 :
    y ∉
      ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3
                  (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                    (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                  (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                    (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 :
    z ∉
      ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3
                  (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                    (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                  (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                    (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 : z ∉ ((syn_ccom (.cv x) (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0032 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0033 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_compose x y
      dv_cache_0001
  have p0001 :=
    @g_elopab
      (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))
      w t (.cv z) dv_cache_0002 dv_cache_0003
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co w t u (.cv x)
      (.cv y) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0003 :=
    @g_eleq2i (syn_ccom (.cv x) (.cv y))
      (syn_copab w t (syn_wex u
          (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))
      (.cv z) p0002
  have p0004 :=
    @g_elima1c w (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                (syn_c1c))) (syn_c1c))) (syn_c1c))
      dv_cache_0013 dv_cache_0014
  have p0005 :=
    @g_elima1c t
      (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
              (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
              (syn_c1c))) (syn_c1c)))
      dv_cache_0015 dv_cache_0016
  have p0006 :=
    @g_elin
      (syn_cop (syn_csn (.cv t))
        (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
      (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
            (syn_cins2 (syn_ccnv (syn_c2nd))))))
      (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
            (syn_c1c))) (syn_c1c))
  have p0007 := @g_vex x
  have p0008 := @g_vex y
  have p0009 := @g_opex (.cv x) (.cv y) p0007 p0008
  have p0010 :=
    @g_oqelins4 (syn_csn (.cv t)) (syn_csn (.cv w)) (syn_csn (.cv z))
      (syn_cop (.cv x) (.cv y))
      (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
          (syn_cins2 (syn_ccnv (syn_c2nd)))))
      p0009
  have p0011 := @g_vex t
  have p0012 := @g_vex w
  have p0013 := @g_vex z
  have p0014 :=
    @g_otsnelsi3 (.cv t) (.cv w) (.cv z)
      (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))
      p0011 p0012 p0013
  have p0015 :=
    @g_elin (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
      (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))
  have p0016 :=
    @g_opelxp (.cv t) (syn_cop (.cv w) (.cv z)) (syn_cvv) (syn_ccnv (syn_c1st))
  have p0017 :=
    @g_mpbiran
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
        (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))))
      (.classMem (.cv t) (syn_cvv))
      (.classMem (syn_cop (.cv w) (.cv z)) (syn_ccnv (syn_c1st))) p0011 p0016
  have p0018 := (Nominal.biimpRefl (syn_wbr (.cv w) (syn_ccnv (syn_c1st)) (.cv z)))
  have p0019 := @g_brcnv (.cv w) (.cv z) (syn_c1st)
  have p0020 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
        (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))))
      (.classMem (syn_cop (.cv w) (.cv z)) (syn_ccnv (syn_c1st)))
      (syn_wbr (.cv w) (syn_ccnv (syn_c1st)) (.cv z)) (syn_wbr (.cv z) (syn_c1st) (.cv w))
      p0017 p0018 p0019
  have p0021 := @g_otelins2 (.cv t) (.cv w) (.cv z) (syn_ccnv (syn_c2nd)) p0012
  have p0022 := (Nominal.biimpRefl (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (.cv z)))
  have p0023 := @g_brcnv (.cv t) (.cv z) (syn_c2nd)
  have p0024 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cins2 (syn_ccnv (syn_c2nd))))
      (.classMem (syn_cop (.cv t) (.cv z)) (syn_ccnv (syn_c2nd)))
      (syn_wbr (.cv t) (syn_ccnv (syn_c2nd)) (.cv z)) (syn_wbr (.cv z) (syn_c2nd) (.cv t))
      p0021 p0022 p0023
  have p0025 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
        (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))))
      (syn_wbr (.cv z) (syn_c1st) (.cv w))
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z))) (syn_cins2 (syn_ccnv (syn_c2nd))))
      (syn_wbr (.cv z) (syn_c2nd) (.cv t)) p0020 p0024
  have p0026 := @g_op1st2nd (.cv w) (.cv t) (.cv z) p0012 p0011
  have p0027 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
        (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))
      (syn_wa (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
          (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))))
        (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
          (syn_cins2 (syn_ccnv (syn_c2nd)))))
      (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv w)) (syn_wbr (.cv z) (syn_c2nd) (.cv t)))
      (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) p0015 p0025 p0026
  have p0028 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
              (syn_cins2 (syn_ccnv (syn_c2nd)))))))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w)) (syn_csn (.cv z))))
        (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
            (syn_cins2 (syn_ccnv (syn_c2nd))))))
      (.classMem (syn_cop (.cv t) (syn_cop (.cv w) (.cv z)))
        (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))))
      (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) p0010 p0014 p0027
  have p0029 :=
    @g_elima1c u
      (syn_cop (syn_csn (.cv t))
        (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
      (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
      dv_cache_0017 dv_cache_0018
  have p0030 :=
    @g_elin
      (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
      (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))
  have p0031 := @g_snex (.cv t)
  have p0032 :=
    @g_otelins2 (syn_csn (.cv u)) (syn_csn (.cv t))
      (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))
      p0031
  have p0033 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t
      (syn_cop (.cv w) (.cv u)) (.cv y) dv_cache_0019 dv_cache_0008)
  have p0034 := (Nominal.biimpRefl (syn_wbr (.cv w) (.cv y) (.cv u)))
  have p0035 :=
    @g_elima1c t
      (syn_cop (syn_csn (.cv u))
        (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      dv_cache_0020 dv_cache_0021
  have p0036 :=
    @g_elin
      (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
      (syn_cins4 (syn_csi3 (syn_cswap)))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
  have p0037 := @g_snex (.cv z)
  have p0038 := @g_opex (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) p0037 p0009
  have p0039 :=
    @g_oqelins4 (syn_csn (.cv t)) (syn_csn (.cv u)) (syn_csn (.cv w))
      (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_csi3 (syn_cswap)) p0038
  have p0040 := @g_vex u
  have p0041 := @g_otsnelsi3 (.cv t) (.cv u) (.cv w) (syn_cswap) p0011 p0040 p0012
  have p0042 :=
    (Nominal.biimpRefl (syn_wbr (.cv t) (syn_cswap) (syn_cop (.cv u) (.cv w))))
  have p0043 := @g_brswap2 (.cv t) (.cv u) (.cv w) p0040 p0012
  have p0044 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv w))))
        (syn_csi3 (syn_cswap)))
      (.classMem (syn_cop (.cv t) (syn_cop (.cv u) (.cv w))) (syn_cswap))
      (syn_wbr (.cv t) (syn_cswap) (syn_cop (.cv u) (.cv w)))
      (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) p0041 p0042 p0043
  have p0045 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins4 (syn_csi3 (syn_cswap))))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv w))))
        (syn_csi3 (syn_cswap)))
      (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) p0039 p0044
  have p0046 := @g_snex (.cv u)
  have p0047 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv u))
      (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) p0046
  have p0048 := @g_snex (.cv w)
  have p0049 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv w))
      (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
      (syn_cins2 (syn_cins2 (syn_csset))) p0048
  have p0050 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))
      (syn_cins2 (syn_csset)) p0037
  have p0051 := @g_otelins2 (syn_csn (.cv t)) (.cv x) (.cv y) (syn_csset) p0007
  have p0052 := @g_opelssetsn (.cv t) (.cv y) p0011 p0008
  have p0053_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv y)) (syn_csset)) (.objMem t y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0052
  have p0053 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv t)) (.cv y)) (syn_csset)) (.objMem t y) p0050
      p0051 p0053_e02_recanon
  have p0054 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      (.classMem
        (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem t y) p0047 p0049 p0053
  have p0055 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins4 (syn_csi3 (syn_cswap))))
      (.classEq (.cv t) (syn_cop (.cv w) (.cv u)))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      (.objMem t y) p0045 p0054
  have p0056 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
              (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
          (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))))
      (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)) p0036 p0055
  have p0057 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))))
      (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)) t p0056
  have p0058 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
      (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv u))
              (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)))
      p0035 p0057
  have p0059_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv w) (.cv u)) (.cv y)) (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)))) :=
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0059 :=
    @g_n_3bitr4ri (.classMem (syn_cop (.cv w) (.cv u)) (.cv y))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv w) (.cv u))) (.objMem t y)))
      (syn_wbr (.cv w) (.cv y) (.cv u))
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
      p0059_e00_recanon p0034 p0058
  have p0060 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))))
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
      (syn_wbr (.cv w) (.cv y) (.cv u)) p0032 p0059
  have p0061 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV v
      (syn_cop (.cv u) (.cv t)) (.cv x) dv_cache_0022 dv_cache_0023)
  have p0062 := (Nominal.biimpRefl (syn_wbr (.cv u) (.cv x) (.cv t)))
  have p0063 :=
    @g_elima1c v
      (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      dv_cache_0024 dv_cache_0025
  have p0064 :=
    @g_elin
      (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
      (syn_cins4 (syn_csi3 (syn_cid)))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
  have p0065 :=
    @g_opex (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) p0048
      p0038
  have p0066 :=
    @g_oqelins4 (syn_csn (.cv v)) (syn_csn (.cv u)) (syn_csn (.cv t))
      (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_csi3 (syn_cid)) p0065
  have p0067 := @g_vex v
  have p0068 := @g_otsnelsi3 (.cv v) (.cv u) (.cv t) (syn_cid) p0067 p0040 p0011
  have p0069 := (Nominal.biimpRefl (syn_wbr (.cv v) (syn_cid) (syn_cop (.cv u) (.cv t))))
  have p0070 := @g_opex (.cv u) (.cv t) p0040 p0011
  have p0071 := @g_ideq (.cv v) (syn_cop (.cv u) (.cv t)) p0070
  have p0072 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv t))))
        (syn_csi3 (syn_cid)))
      (.classMem (syn_cop (.cv v) (syn_cop (.cv u) (.cv t))) (syn_cid))
      (syn_wbr (.cv v) (syn_cid) (syn_cop (.cv u) (.cv t)))
      (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) p0068 p0069 p0071
  have p0073 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u)) (syn_csn (.cv t))))
        (syn_csi3 (syn_cid)))
      (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) p0066 p0072
  have p0074 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv u))
      (syn_cop (syn_csn (.cv t))
        (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) p0046
  have p0075 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv t))
      (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0031
  have p0076 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv w))
      (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
      (syn_cins2 (syn_cins3 (syn_csset))) p0048
  have p0077 :=
    @g_otelins2 (syn_csn (.cv v)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))
      (syn_cins3 (syn_csset)) p0037
  have p0078 := @g_otelins3 (syn_csn (.cv v)) (.cv x) (.cv y) (syn_csset) p0008
  have p0079 := @g_opelssetsn (.cv v) (.cv x) p0067 p0007
  have p0080_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv v)) (.cv x)) (syn_csset)) (.objMem v x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0079
  have p0080 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv v)) (.cv x)) (syn_csset)) (.objMem v x) p0078
      p0080_e01_recanon
  have p0081 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
        (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))
      (.classMem
        (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins3 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)))
      (.objMem v x) p0076 p0077 p0080
  have p0082 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
        (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))
      (.objMem v x) p0074 p0075 p0081
  have p0083 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classEq (.cv v) (syn_cop (.cv u) (.cv t)))
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      (.objMem v x) p0073 p0082
  have p0084 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
              (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                  (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
          (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv v))
            (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                  (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))))
      (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)) p0064 p0083
  have p0085 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
            (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))))
      (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)) v p0084
  have p0086 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
      (syn_wex v (.classMem (syn_cop (syn_csn (.cv v)) (syn_cop (syn_csn (.cv u))
              (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
                  (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))))
      (syn_wex v (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)))
      p0063 p0085
  have p0087_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv u) (.cv t)) (.cv x)) (syn_wex v
          (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)))) :=
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0061
  have p0087 :=
    @g_n_3bitr4ri (.classMem (syn_cop (.cv u) (.cv t)) (.cv x))
      (syn_wex v (syn_wa (.classEq (.cv v) (syn_cop (.cv u) (.cv t))) (.objMem v x)))
      (syn_wbr (.cv u) (.cv x) (.cv t))
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
      p0087_e00_recanon p0062 p0086
  have p0088 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))))
      (syn_wbr (.cv w) (.cv y) (.cv u))
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
      (syn_wbr (.cv u) (.cv x) (.cv t)) p0060 p0087
  have p0089 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
            (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
              (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cins2 (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))))
        (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
              (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
            (syn_c1c))))
      (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))) p0030
      p0088
  have p0090 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))))
        (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
            (syn_c1c))))
      (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))) u p0089
  have p0091 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin
            (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
              (syn_c1c))) (syn_c1c)))
      (syn_wex u (.classMem (syn_cop (syn_csn (.cv u)) (syn_cop (syn_csn (.cv t))
              (syn_cop (syn_csn (.cv w))
                (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))) (syn_cin (syn_cins2
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
              (syn_c1c)))))
      (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))
      p0029 p0090
  have p0092 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
              (syn_cins2 (syn_ccnv (syn_c2nd)))))))
      (.classEq (.cv z) (syn_cop (.cv w) (.cv t)))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cima (syn_cin
            (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
              (syn_c1c))) (syn_c1c)))
      (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))
      p0028 p0091
  have p0093 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4
            (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                (syn_c1c))) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
              (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                (syn_cins2 (syn_ccnv (syn_c2nd))))))) (.classMem (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))))
          (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                (syn_c1c))) (syn_c1c))))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u
          (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))
      p0006 p0092
  have p0094 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4
            (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                (syn_c1c))) (syn_c1c))))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u
          (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))
      t p0093
  have p0095 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                  (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv w))
              (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))) (syn_cin (syn_cins4
              (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                  (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
              (syn_c1c)))))
      (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u
            (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))))
      p0005 p0094
  have p0096 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                  (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)))
      (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u
            (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t))))))
      w p0095
  have p0097 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                    (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                  (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                    (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c)))
      (syn_wex w (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cima (syn_cin (syn_cins4
                (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                    (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                  (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                    (syn_c1c))) (syn_c1c))) (syn_c1c))))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u
              (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))))
      p0004 p0096
  have p0098 :=
    @g_n_3bitr4ri
      (.classMem (.cv z) (syn_copab w t (syn_wex u (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u))
              (syn_wbr (.cv u) (.cv x) (.cv t))))))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_cop (.cv w) (.cv t))) (syn_wex u
              (syn_wa (syn_wbr (.cv w) (.cv y) (.cv u)) (syn_wbr (.cv u) (.cv x) (.cv t)))))))
      (.classMem (.cv z) (syn_ccom (.cv x) (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                    (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                  (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                    (syn_c1c))) (syn_c1c))) (syn_c1c)) (syn_c1c)))
      p0001 p0003 p0097
  have p0099 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv)
      (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                  (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)) (syn_c1c))
      (syn_ccom (.cv x) (.cv y)) dv_cache_0026 dv_cache_0027 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0001 dv_cache_0032
      dv_cache_0033 p0098
  have p0100 :=
    @g_eqtr4i (syn_ccompose)
      (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_ccom (.cv x) (.cv y)))
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cima (syn_cin
                    (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                          (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2
                          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
                            (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2
                                (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
                      (syn_c1c))) (syn_c1c)) (syn_c1c)))) (syn_c1c)))
      p0000 p0099
  have p0101 := @g_vvex
  have p0104 := @g_n_1stex
  have p0105 := @g_cnvex (syn_c1st) p0104
  have p0106 := @g_xpex (syn_cvv) (syn_ccnv (syn_c1st)) p0101 p0105
  have p0107 := @g_n_2ndex
  have p0108 := @g_cnvex (syn_c2nd) p0107
  have p0109 := @g_ins2ex (syn_ccnv (syn_c2nd)) p0108
  have p0110 :=
    @g_inex (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd)))
      p0106 p0109
  have p0111 :=
    @g_si3ex
      (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st))) (syn_cins2 (syn_ccnv (syn_c2nd))))
      p0110
  have p0112 :=
    @g_ins4ex
      (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
          (syn_cins2 (syn_ccnv (syn_c2nd)))))
      p0111
  have p0113 := @g_swapex
  have p0114 := @g_si3ex (syn_cswap) p0113
  have p0115 := @g_ins4ex (syn_csi3 (syn_cswap)) p0114
  have p0116 := @g_ssetex
  have p0117 := @g_ins2ex (syn_csset) p0116
  have p0118 := @g_ins2ex (syn_cins2 (syn_csset)) p0117
  have p0119 := @g_ins2ex (syn_cins2 (syn_cins2 (syn_csset))) p0118
  have p0120 := @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) p0119
  have p0121 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cswap)))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) p0115 p0120
  have p0122 := @g_n_1cex
  have p0123 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_c1c) p0121 p0122
  have p0124 :=
    @g_ins2ex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))
      p0123
  have p0125 := @g_idex
  have p0126 := @g_si3ex (syn_cid) p0125
  have p0127 := @g_ins4ex (syn_csi3 (syn_cid)) p0126
  have p0129 := @g_ins3ex (syn_csset) p0116
  have p0130 := @g_ins2ex (syn_cins3 (syn_csset)) p0129
  have p0131 := @g_ins2ex (syn_cins2 (syn_cins3 (syn_csset))) p0130
  have p0132 := @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))) p0131
  have p0133 :=
    @g_ins2ex (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))) p0132
  have p0134 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid)))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))) p0127 p0133
  have p0136 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
      (syn_c1c) p0134 p0122
  have p0137 :=
    @g_inex
      (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c))
      p0124 p0136
  have p0139 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
      (syn_c1c) p0137 p0122
  have p0140 :=
    @g_inex
      (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
            (syn_cins2 (syn_ccnv (syn_c2nd))))))
      (syn_cima (syn_cin (syn_cins2 (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
            (syn_c1c))) (syn_c1c))
      p0112 p0139
  have p0142 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
              (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
              (syn_c1c))) (syn_c1c)))
      (syn_c1c) p0140 p0122
  have p0144 :=
    @g_imaex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
              (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset)))))))
                (syn_c1c))) (syn_c1c))) (syn_c1c))
      (syn_c1c) p0142 p0122
  have p0145 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv)
      (syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3
                (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                  (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2 (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))) (syn_c1c)))
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
              (syn_c1c))) (syn_c1c)) (syn_c1c))
      p0101 p0101 p0144
  have p0146 :=
    @g_eqeltri (syn_ccompose)
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cima (syn_cin
                    (syn_cins4 (syn_csi3 (syn_cin (syn_cxp (syn_cvv) (syn_ccnv (syn_c1st)))
                          (syn_cins2 (syn_ccnv (syn_c2nd)))))) (syn_cima (syn_cin (syn_cins2
                          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
                            (syn_c1c))) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2
                                (syn_cins2 (syn_cins2 (syn_cins3 (syn_csset))))))) (syn_c1c)))
                      (syn_c1c))) (syn_c1c)) (syn_c1c)))) (syn_c1c)))
      (syn_cvv) p0100 p0145
  exact p0146


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_brdisjg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (syn_wbr A (syn_cdisj) B) (.classEq (syn_cin A B) (syn_c0)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_ineq1 (.cv x) A (.cv y)
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) A) (syn_cin (.cv x) (.cv y)) (syn_cin A (.cv y)) (syn_c0)
      p0000
  have p0002 := @g_ineq2 (.cv y) B A
  have p0003 :=
    @g_eqeq1d (.classEq (.cv y) B) (syn_cin A (.cv y)) (syn_cin A B) (syn_c0) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_disj x y
      dv_cache_0001
  have p0005 :=
    @g_brabg (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))
      (.classEq (syn_cin A (.cv y)) (syn_c0)) (.classEq (syn_cin A B) (syn_c0)) x y A B V
      W (syn_cdisj) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0001 p0003 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
