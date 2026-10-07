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

/-- Checked nominal proof certificate identified upstream as `g_otsnelsi3`. -/
@[expose]
noncomputable def gOtsnelsi3 (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_otsnelsi3_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_otsnelsi3_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_otsnelsi3_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn A) (synCop (synCsn B) (synCsn C))) (synCsi3 R))
        (.classMem (synCop A (synCop B C)) R)) :=
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
  have dv_cache_0001 : p ∉ ((synCop (synCsn A) (synCop (synCsn B) (synCsn C)))).fv :=
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
      ((synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
            (synCsi (synCcom (synC2nd) (synC2nd)))))).fv :=
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
  have dv_cache_0006 : x ∉ ((synC1st)).fv :=
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
  have dv_cache_0007 : x ∉ ((synC2nd)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCproj2 (.cv p))).fv :=
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
  have dv_cache_0009 : x ∉ ((synWbr (synCproj2 (.cv p)) (synC1st) B)).fv :=
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
  have dv_cache_0011 : x ∉ ((synWbr (synCproj2 (.cv p)) (synC2nd) C)).fv :=
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
  have dv_cache_0012 : p ∉ ((synCop A (synCop B C))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synCsi3 R))
  have p0001 :=
    @gEleq2i (synCsi3 R)
      (synCima (synCtxp (synCsi (synC1st))
          (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
            (synCsi (synCcom (synC2nd) (synC2nd))))) (synCpw1 R))
      (synCop (synCsn A) (synCop (synCsn B) (synCsn C))) p0000
  have p0002 :=
    @gElimapw1 p (synCop (synCsn A) (synCop (synCsn B) (synCsn C)))
      (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
          (synCsi (synCcom (synC2nd) (synC2nd)))))
      R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @gOteltxp (synCsn (.cv p)) (synCsn A) (synCop (synCsn B) (synCsn C))
      (synCsi (synC1st))
      (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
        (synCsi (synCcom (synC2nd) (synC2nd))))
  have p0004 := @gVex p
  have p0005 := @gOpsnelsi (.cv p) A (synC1st) p0004 hyp_otsnelsi3_1
  have p0006 := (Nominal.biimpRefl (synWbr (.cv p) (synC1st) A))
  have p0007 :=
    @gBitr4i (.classMem (synCop (synCsn (.cv p)) (synCsn A)) (synCsi (synC1st)))
      (.classMem (synCop (.cv p) A) (synC1st)) (synWbr (.cv p) (synC1st) A) p0005
      p0006
  have p0008 :=
    @gOteltxp (synCsn (.cv p)) (synCsn B) (synCsn C)
      (synCsi (synCcom (synC1st) (synC2nd)))
      (synCsi (synCcom (synC2nd) (synC2nd)))
  have p0009 :=
    @gOpsnelsi (.cv p) B (synCcom (synC1st) (synC2nd)) p0004 hyp_otsnelsi3_2
  have p0010 :=
    @gOpelco x (.cv p) B (synC1st) (synC2nd) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0011 := @gOpeq (.cv p)
  have p0012 :=
    @gBreq1i (.cv p) (synCop (synCproj1 (.cv p)) (synCproj2 (.cv p))) (.cv x)
      (synC2nd) p0011
  have p0013 := @gProj1ex (.cv p) p0004
  have p0014 := @gProj2ex (.cv p) p0004
  have p0015 := @gOpbr2nd (synCproj1 (.cv p)) (synCproj2 (.cv p)) (.cv x) p0013 p0014
  have p0016 := @gEqcom (synCproj2 (.cv p)) (.cv x)
  have p0017 :=
    @gN3bitri (synWbr (.cv p) (synC2nd) (.cv x))
      (synWbr (synCop (synCproj1 (.cv p)) (synCproj2 (.cv p))) (synC2nd) (.cv x))
      (.classEq (synCproj2 (.cv p)) (.cv x)) (.classEq (.cv x) (synCproj2 (.cv p)))
      p0012 p0015 p0016
  have p0018 :=
    @gAnbi1i (synWbr (.cv p) (synC2nd) (.cv x)) (.classEq (.cv x) (synCproj2 (.cv p)))
      (synWbr (.cv x) (synC1st) B) p0017
  have p0019 :=
    @gExbii (synWa (synWbr (.cv p) (synC2nd) (.cv x)) (synWbr (.cv x) (synC1st) B))
      (synWa (.classEq (.cv x) (synCproj2 (.cv p))) (synWbr (.cv x) (synC1st) B)) x
      p0018
  have p0020 := @gBreq1 (.cv x) (synCproj2 (.cv p)) B (synC1st)
  have p0021 :=
    @gCeqsexv (synWbr (.cv x) (synC1st) B) (synWbr (synCproj2 (.cv p)) (synC1st) B)
      x (synCproj2 (.cv p)) dv_cache_0008 dv_cache_0009 p0014 p0020
  have p0022 :=
    @gBitri
      (synWex x (synWa (synWbr (.cv p) (synC2nd) (.cv x)) (synWbr (.cv x) (synC1st) B)))
      (synWex x
        (synWa (.classEq (.cv x) (synCproj2 (.cv p))) (synWbr (.cv x) (synC1st) B)))
      (synWbr (synCproj2 (.cv p)) (synC1st) B) p0019 p0021
  have p0023 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p)) (synCsn B))
        (synCsi (synCcom (synC1st) (synC2nd))))
      (.classMem (synCop (.cv p) B) (synCcom (synC1st) (synC2nd)))
      (synWex x (synWa (synWbr (.cv p) (synC2nd) (.cv x)) (synWbr (.cv x) (synC1st) B)))
      (synWbr (synCproj2 (.cv p)) (synC1st) B) p0009 p0010 p0022
  have p0024 :=
    @gOpsnelsi (.cv p) C (synCcom (synC2nd) (synC2nd)) p0004 hyp_otsnelsi3_3
  have p0025 :=
    @gOpelco x (.cv p) C (synC2nd) (synC2nd) dv_cache_0004 dv_cache_0010 dv_cache_0007
      dv_cache_0007
  have p0026 :=
    @gAnbi1i (synWbr (.cv p) (synC2nd) (.cv x)) (.classEq (.cv x) (synCproj2 (.cv p)))
      (synWbr (.cv x) (synC2nd) C) p0017
  have p0027 :=
    @gExbii (synWa (synWbr (.cv p) (synC2nd) (.cv x)) (synWbr (.cv x) (synC2nd) C))
      (synWa (.classEq (.cv x) (synCproj2 (.cv p))) (synWbr (.cv x) (synC2nd) C)) x
      p0026
  have p0028 := @gBreq1 (.cv x) (synCproj2 (.cv p)) C (synC2nd)
  have p0029 :=
    @gCeqsexv (synWbr (.cv x) (synC2nd) C) (synWbr (synCproj2 (.cv p)) (synC2nd) C)
      x (synCproj2 (.cv p)) dv_cache_0008 dv_cache_0011 p0014 p0028
  have p0030 :=
    @gBitri
      (synWex x (synWa (synWbr (.cv p) (synC2nd) (.cv x)) (synWbr (.cv x) (synC2nd) C)))
      (synWex x
        (synWa (.classEq (.cv x) (synCproj2 (.cv p))) (synWbr (.cv x) (synC2nd) C)))
      (synWbr (synCproj2 (.cv p)) (synC2nd) C) p0027 p0029
  have p0031 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p)) (synCsn C))
        (synCsi (synCcom (synC2nd) (synC2nd))))
      (.classMem (synCop (.cv p) C) (synCcom (synC2nd) (synC2nd)))
      (synWex x (synWa (synWbr (.cv p) (synC2nd) (.cv x)) (synWbr (.cv x) (synC2nd) C)))
      (synWbr (synCproj2 (.cv p)) (synC2nd) C) p0024 p0025 p0030
  have p0032 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv p)) (synCsn B))
        (synCsi (synCcom (synC1st) (synC2nd))))
      (synWbr (synCproj2 (.cv p)) (synC1st) B)
      (.classMem (synCop (synCsn (.cv p)) (synCsn C))
        (synCsi (synCcom (synC2nd) (synC2nd))))
      (synWbr (synCproj2 (.cv p)) (synC2nd) C) p0023 p0031
  have p0033 :=
    @gOpbr2nd (synCproj1 (.cv p)) (synCproj2 (.cv p)) (synCop B C) p0013 p0014
  have p0034 :=
    @gBreq1i (.cv p) (synCop (synCproj1 (.cv p)) (synCproj2 (.cv p))) (synCop B C)
      (synC2nd) p0011
  have p0035 := @gOp1st2nd B C (synCproj2 (.cv p)) hyp_otsnelsi3_2 hyp_otsnelsi3_3
  have p0036 :=
    @gN3bitr4ri
      (synWbr (synCop (synCproj1 (.cv p)) (synCproj2 (.cv p))) (synC2nd) (synCop B C))
      (.classEq (synCproj2 (.cv p)) (synCop B C))
      (synWbr (.cv p) (synC2nd) (synCop B C))
      (synWa (synWbr (synCproj2 (.cv p)) (synC1st) B)
        (synWbr (synCproj2 (.cv p)) (synC2nd) C))
      p0033 p0034 p0035
  have p0037 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn B) (synCsn C)))
        (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
          (synCsi (synCcom (synC2nd) (synC2nd)))))
      (synWa (.classMem (synCop (synCsn (.cv p)) (synCsn B))
          (synCsi (synCcom (synC1st) (synC2nd))))
        (.classMem (synCop (synCsn (.cv p)) (synCsn C))
          (synCsi (synCcom (synC2nd) (synC2nd)))))
      (synWa (synWbr (synCproj2 (.cv p)) (synC1st) B)
        (synWbr (synCproj2 (.cv p)) (synC2nd) C))
      (synWbr (.cv p) (synC2nd) (synCop B C)) p0008 p0032 p0036
  have p0038 :=
    @gAnbi12i (.classMem (synCop (synCsn (.cv p)) (synCsn A)) (synCsi (synC1st)))
      (synWbr (.cv p) (synC1st) A)
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn B) (synCsn C)))
        (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
          (synCsi (synCcom (synC2nd) (synC2nd)))))
      (synWbr (.cv p) (synC2nd) (synCop B C)) p0007 p0037
  have p0039 := @gOpex B C hyp_otsnelsi3_2 hyp_otsnelsi3_3
  have p0040 := @gOp1st2nd A (synCop B C) (.cv p) hyp_otsnelsi3_1 p0039
  have p0041 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn A) (synCop (synCsn B) (synCsn C))))
        (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
            (synCsi (synCcom (synC2nd) (synC2nd))))))
      (synWa (.classMem (synCop (synCsn (.cv p)) (synCsn A)) (synCsi (synC1st)))
        (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn B) (synCsn C)))
          (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
            (synCsi (synCcom (synC2nd) (synC2nd))))))
      (synWa (synWbr (.cv p) (synC1st) A) (synWbr (.cv p) (synC2nd) (synCop B C)))
      (.classEq (.cv p) (synCop A (synCop B C))) p0003 p0038 p0040
  have p0042 :=
    @gRexbii
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn A) (synCop (synCsn B) (synCsn C))))
        (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
            (synCsi (synCcom (synC2nd) (synC2nd))))))
      (.classEq (.cv p) (synCop A (synCop B C))) p R p0041
  have p0043 := @gRisset p (synCop A (synCop B C)) R dv_cache_0012 dv_cache_0003
  have p0044 :=
    @gBitr4i
      (synWrex p R (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn A) (synCop (synCsn B) (synCsn C))))
          (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
              (synCsi (synCcom (synC2nd) (synC2nd)))))))
      (synWrex p R (.classEq (.cv p) (synCop A (synCop B C))))
      (.classMem (synCop A (synCop B C)) R) p0042 p0043
  have p0045 :=
    @gN3bitri
      (.classMem (synCop (synCsn A) (synCop (synCsn B) (synCsn C))) (synCsi3 R))
      (.classMem (synCop (synCsn A) (synCop (synCsn B) (synCsn C))) (synCima
          (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
              (synCsi (synCcom (synC2nd) (synC2nd))))) (synCpw1 R)))
      (synWrex p R (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn A) (synCop (synCsn B) (synCsn C))))
          (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
              (synCsi (synCcom (synC2nd) (synC2nd)))))))
      (.classMem (synCop A (synCop B C)) R) p0001 p0002 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_si3ex`. -/
@[expose]
noncomputable def gSi3ex (A : Class)
    (hyp_si3ex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCsi3 A) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCsi3 A))
  have p0001 := @gN1stex
  have p0002 := @gSiex (synC1st) p0001
  have p0004 := @gN2ndex
  have p0005 := @gCoex (synC1st) (synC2nd) p0001 p0004
  have p0006 := @gSiex (synCcom (synC1st) (synC2nd)) p0005
  have p0009 := @gCoex (synC2nd) (synC2nd) p0004 p0004
  have p0010 := @gSiex (synCcom (synC2nd) (synC2nd)) p0009
  have p0011 :=
    @gTxpex (synCsi (synCcom (synC1st) (synC2nd)))
      (synCsi (synCcom (synC2nd) (synC2nd))) p0006 p0010
  have p0012 :=
    @gTxpex (synCsi (synC1st))
      (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
        (synCsi (synCcom (synC2nd) (synC2nd))))
      p0002 p0011
  have p0013 := @gPw1ex A hyp_si3ex_1
  have p0014 :=
    @gImaex
      (synCtxp (synCsi (synC1st)) (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
          (synCsi (synCcom (synC2nd) (synC2nd)))))
      (synCpw1 A) p0012 p0013
  have p0015 :=
    @gEqeltri (synCsi3 A)
      (synCima (synCtxp (synCsi (synC1st))
          (synCtxp (synCsi (synCcom (synC1st) (synC2nd)))
            (synCsi (synCcom (synC2nd) (synC2nd))))) (synCpw1 A))
      (synCvv) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_releqel`. -/
@[expose]
noncomputable def gReleqel (x : Var) (y : Var) (A : Class) (R : Class) (T : Class)
    (dv_A_y : y ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_T_y : y ∉ T.fv) (dv_x_y : x ≠ y)
    (hyp_releqel_1 : Nominal.NPrf (.classMem T (synCvv)))
    (hyp_releqel_2 : Nominal.NPrf
        (synWb (.classMem (synCop (synCsn (.cv y)) T) R) (.classMem (.cv y) A))) :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) T) (synCcompl
            (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))
        (.classEq (.cv x) A)) :=
  by
  have dv_cache_0001 : y ∉ ((synCop (.cv x) T)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_T_y, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCsymdif (synCins3 (synCsset)) (synCins2 R))).fv :=
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
    @gElima1c y (synCop (.cv x) T) (synCsymdif (synCins3 (synCsset)) (synCins2 R))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gElsymdif (synCop (synCsn (.cv y)) (synCop (.cv x) T)) (synCins3 (synCsset))
      (synCins2 R)
  have p0002 := @gOtelins3 (synCsn (.cv y)) (.cv x) T (synCsset) hyp_releqel_1
  have p0003 := @gVex y
  have p0004 := @gVex x
  have p0005 := @gOpelssetsn (.cv y) (.cv x) p0003 p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCsset)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T)) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCsset)) (.objMem y x) p0002
      p0006_e01_recanon
  have p0007 := @gOtelins2 (synCsn (.cv y)) (.cv x) T R p0004
  have p0008 :=
    @gBitri (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T)) (synCins2 R))
      (.classMem (synCop (synCsn (.cv y)) T) R) (.classMem (.cv y) A) p0007
      hyp_releqel_2
  have p0009 :=
    @gBibi12i
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T)) (synCins3 (synCsset)))
      (.objMem y x)
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T)) (synCins2 R))
      (.classMem (.cv y) A) p0006 p0008
  have p0010 :=
    @gXchbinx
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T))
        (synCsymdif (synCins3 (synCsset)) (synCins2 R)))
      (synWb (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T))
          (synCins3 (synCsset)))
        (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T)) (synCins2 R)))
      (synWb (.objMem y x) (.classMem (.cv y) A)) p0001 p0009
  have p0011 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T))
        (synCsymdif (synCins3 (synCsset)) (synCins2 R)))
      (.neg (synWb (.objMem y x) (.classMem (.cv y) A))) y p0010
  have p0012 := @gExnal (synWb (.objMem y x) (.classMem (.cv y) A)) y
  have p0013 :=
    @gN3bitrri
      (.classMem (synCop (.cv x) T)
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))
      (synWex y (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) T))
          (synCsymdif (synCins3 (synCsset)) (synCins2 R))))
      (synWex y (.neg (synWb (.objMem y x) (.classMem (.cv y) A))))
      (.neg (.all y (synWb (.objMem y x) (.classMem (.cv y) A)))) p0000 p0011 p0012
  have p0014 :=
    @gCon1bii (.all y (synWb (.objMem y x) (.classMem (.cv y) A)))
      (.classMem (synCop (.cv x) T)
        (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))
      p0013
  have p0015 := @gOpex (.cv x) T p0004 hyp_releqel_1
  have p0016 :=
    @gElcompl (synCop (.cv x) T)
      (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)) p0015
  have p0017 := @gDfcleq y (.cv x) A dv_cache_0003 dv_cache_0004
  have p0018_e02_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv x) A) (.all y (synWb (.objMem y x) (.classMem (.cv y) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gN3bitr4i
      (.neg (.classMem (synCop (.cv x) T)
          (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))
      (.all y (synWb (.objMem y x) (.classMem (.cv y) A)))
      (.classMem (synCop (.cv x) T) (synCcompl
          (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))
      (.classEq (.cv x) A) p0014 p0016 p0018_e02_recanon
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_releqmpt`. -/
@[expose]
noncomputable def gReleqmpt (x : Var) (y : Var) (A : Class) (R : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_V_y : y ∉ V.fv)
    (dv_x_y : x ≠ y)
    (hyp_releqmpt_1 : Nominal.NPrf (synWb (.classMem (synCop (synCsn (.cv y)) (.cv x)) R)
          (.classMem (.cv y) V))) :
    Nominal.NPrf
      (.classEq (synCin (synCxp A (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))
        (synCmpt x A V)) :=
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
      ((synCin (synCxp A (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))).fv :=
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
      ((synCin (synCxp A (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))).fv :=
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
    @gElin (synCop (.cv x) (.cv z)) (synCxp A (synCvv))
      (synCcnv (synCcompl
          (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))
  have p0001 := @gVex z
  have p0002 := @gOpelxp (.cv x) (.cv z) A (synCvv)
  have p0003 :=
    @gMpbiran2 (.classMem (synCop (.cv x) (.cv z)) (synCxp A (synCvv)))
      (.classMem (.cv x) A) (.classMem (.cv z) (synCvv)) p0001 p0002
  have p0004 :=
    @gOpelcnv (.cv x) (.cv z)
      (synCcompl (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))
  have p0005 := @gVex x
  have p0006 :=
    @gReleqel z y V R (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      p0005 hyp_releqmpt_1
  have p0007 :=
    @gBitri
      (.classMem (synCop (.cv x) (.cv z)) (synCcnv (synCcompl
            (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))
      (.classMem (synCop (.cv z) (.cv x)) (synCcompl
          (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))
      (.classEq (.cv z) V) p0004 p0006
  have p0008 :=
    @gAnbi12i (.classMem (synCop (.cv x) (.cv z)) (synCxp A (synCvv)))
      (.classMem (.cv x) A)
      (.classMem (synCop (.cv x) (.cv z)) (synCcnv (synCcompl
            (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))
      (.classEq (.cv z) V) p0003 p0007
  have p0009 :=
    @gBitri
      (.classMem (synCop (.cv x) (.cv z)) (synCin (synCxp A (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))))
      (synWa (.classMem (synCop (.cv x) (.cv z)) (synCxp A (synCvv)))
        (.classMem (synCop (.cv x) (.cv z)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))))
      (synWa (.classMem (.cv x) A) (.classEq (.cv z) V)) p0000 p0008
  have p0010 :=
    @gOpabbi2i (synWa (.classMem (.cv x) A) (.classEq (.cv z) V)) x z
      (synCin (synCxp A (synCvv)) (synCcnv (synCcompl
            (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x z A V
      dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0012 :=
    @gEqtr4i
      (synCin (synCxp A (synCvv)) (synCcnv (synCcompl
            (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))
      (synCopab x z (synWa (.classMem (.cv x) A) (.classEq (.cv z) V))) (synCmpt x A V)
      p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_releqmpt2`. -/
@[expose]
noncomputable def gReleqmpt2 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (R : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_V_z : z ∉ V.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_releqmpt2_1 : Nominal.NPrf
        (synWb (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) R)
          (.classMem (.cv z) V))) :
    Nominal.NPrf
      (.classEq (synCdif (synCxp (synCxp A B) (synCvv))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))
        (synCmpt2 x A y B V)) :=
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
  have dv_cache_0003 : z ∉ ((synCop (synCop (.cv x) (.cv y)) (.cv w))).fv :=
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
  have dv_cache_0004 : z ∉ ((synCsymdif (synCins2 (synCsset)) (synCins3 R))).fv :=
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
      ((synCdif (synCxp (synCxp A B) (synCvv))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))).fv :=
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
      ((synCdif (synCxp (synCxp A B) (synCvv))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))).fv :=
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
      ((synCdif (synCxp (synCxp A B) (synCvv))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))).fv :=
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
    @gEldif (synCop (synCop (.cv x) (.cv y)) (.cv w)) (synCxp (synCxp A B) (synCvv))
      (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c))
  have p0001 := @gVex w
  have p0002 := @gOpelxp (synCop (.cv x) (.cv y)) (.cv w) (synCxp A B) (synCvv)
  have p0003 :=
    @gMpbiran2
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w)) (synCxp (synCxp A B) (synCvv)))
      (.classMem (synCop (.cv x) (.cv y)) (synCxp A B)) (.classMem (.cv w) (synCvv))
      p0001 p0002
  have p0004 := @gOpelxp (.cv x) (.cv y) A B
  have p0005 :=
    @gBitri
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w)) (synCxp (synCxp A B) (synCvv)))
      (.classMem (synCop (.cv x) (.cv y)) (synCxp A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0003 p0004
  have p0006 := @gDfcleq z (.cv w) V dv_cache_0001 dv_cache_0002
  have p0007 :=
    @gElima1c z (synCop (synCop (.cv x) (.cv y)) (.cv w))
      (synCsymdif (synCins2 (synCsset)) (synCins3 R)) dv_cache_0003 dv_cache_0004
  have p0008 :=
    @gElsymdif (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
      (synCins2 (synCsset)) (synCins3 R)
  have p0009 := @gVex x
  have p0010 := @gVex y
  have p0011 := @gOpex (.cv x) (.cv y) p0009 p0010
  have p0012 :=
    @gOtelins2 (synCsn (.cv z)) (synCop (.cv x) (.cv y)) (.cv w) (synCsset) p0011
  have p0013 := @gVex z
  have p0014 := @gOpelssetsn (.cv z) (.cv w) p0013 p0001
  have p0015_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv w)) (synCsset)) (.objMem z w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv w)) (synCsset)) (.objMem z w) p0012
      p0015_e01_recanon
  have p0016 := @gOtelins3 (synCsn (.cv z)) (synCop (.cv x) (.cv y)) (.cv w) R p0001
  have p0017 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
        (synCins3 R))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) R)
      (.classMem (.cv z) V) p0016 hyp_releqmpt2_1
  have p0018 :=
    @gBibi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
        (synCins2 (synCsset)))
      (.objMem z w)
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
        (synCins3 R))
      (.classMem (.cv z) V) p0015 p0017
  have p0019 :=
    @gXchbinx
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
        (synCsymdif (synCins2 (synCsset)) (synCins3 R)))
      (synWb (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
          (synCins2 (synCsset)))
        (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
          (synCins3 R)))
      (synWb (.objMem z w) (.classMem (.cv z) V)) p0008 p0018
  have p0020 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
        (synCsymdif (synCins2 (synCsset)) (synCins3 R)))
      (.neg (synWb (.objMem z w) (.classMem (.cv z) V))) z p0019
  have p0021 := @gExnal (synWb (.objMem z w) (.classMem (.cv z) V)) z
  have p0022 :=
    @gN3bitri
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))
      (synWex z
        (.classMem (synCop (synCsn (.cv z)) (synCop (synCop (.cv x) (.cv y)) (.cv w)))
          (synCsymdif (synCins2 (synCsset)) (synCins3 R))))
      (synWex z (.neg (synWb (.objMem z w) (.classMem (.cv z) V))))
      (.neg (.all z (synWb (.objMem z w) (.classMem (.cv z) V)))) p0007 p0020 p0021
  have p0023 :=
    @gCon2bii
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))
      (.all z (synWb (.objMem z w) (.classMem (.cv z) V))) p0022
  have p0024_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv w) V) (.all z (synWb (.objMem z w) (.classMem (.cv z) V)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gBitr2i (.classEq (.cv w) V) (.all z (synWb (.objMem z w) (.classMem (.cv z) V)))
      (.neg (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c))))
      p0024_e00_recanon p0023
  have p0025 :=
    @gAnbi12i
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w)) (synCxp (synCxp A B) (synCvv)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (.neg (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c))))
      (.classEq (.cv w) V) p0005 p0024
  have p0026 :=
    @gBitri
      (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
        (synCdif (synCxp (synCxp A B) (synCvv))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c))))
      (synWa (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
          (synCxp (synCxp A B) (synCvv))) (.neg
          (.classMem (synCop (synCop (.cv x) (.cv y)) (.cv w))
            (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V))
      p0000 p0025
  have p0027 :=
    @gOprabbi2i
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) V)) x
      y w
      (synCdif (synCxp (synCxp A B) (synCvv))
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      p0026
  have p0028 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt2 x y w A B V
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0009 dv_cache_0010
  have p0029 :=
    @gEqtr4i
      (synCdif (synCxp (synCxp A B) (synCvv))
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))
      (synCoprab x y w (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv w) V)))
      (synCmpt2 x A y B V) p0027 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_mptexlem`. -/
@[expose]
noncomputable def gMptexlem (A : Class) (R : Class)
    (hyp_mptexlem_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_mptexlem_2 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.classMem (synCin (synCxp A (synCvv)) (synCcnv (synCcompl
              (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))))
        (synCvv)) :=
  by
  have p0000 := @gVvex
  have p0001 := @gXpex A (synCvv) hyp_mptexlem_1 p0000
  have p0002 := @gSsetex
  have p0003 := @gIns3ex (synCsset) p0002
  have p0004 := @gIns2ex R hyp_mptexlem_2
  have p0005 := @gSymdifex (synCins3 (synCsset)) (synCins2 R) p0003 p0004
  have p0006 := @gN1cex
  have p0007 :=
    @gImaex (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c) p0005 p0006
  have p0008 :=
    @gComplex (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))
      p0007
  have p0009 :=
    @gCnvex
      (synCcompl (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c)))
      p0008
  have p0010 :=
    @gInex (synCxp A (synCvv))
      (synCcnv (synCcompl
          (synCima (synCsymdif (synCins3 (synCsset)) (synCins2 R)) (synC1c))))
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

/-- Checked nominal proof certificate identified upstream as `g_mpt2exlem`. -/
@[expose]
noncomputable def gMpt2exlem (A : Class) (B : Class) (R : Class)
    (hyp_mpt2exlem_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_mpt2exlem_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_mpt2exlem_3 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf
      (.classMem (synCdif (synCxp (synCxp A B) (synCvv))
          (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)))
        (synCvv)) :=
  by
  have p0000 := @gXpex A B hyp_mpt2exlem_1 hyp_mpt2exlem_2
  have p0001 := @gVvex
  have p0002 := @gXpex (synCxp A B) (synCvv) p0000 p0001
  have p0003 := @gSsetex
  have p0004 := @gIns2ex (synCsset) p0003
  have p0005 := @gIns3ex R hyp_mpt2exlem_3
  have p0006 := @gSymdifex (synCins2 (synCsset)) (synCins3 R) p0004 p0005
  have p0007 := @gN1cex
  have p0008 :=
    @gImaex (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c) p0006 p0007
  have p0009 :=
    @gDifex (synCxp (synCxp A B) (synCvv))
      (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 R)) (synC1c)) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_cupvalg`. -/
@[expose]
noncomputable def gCupvalg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (.classEq (synCo A (synCcup) B) (synCun A B))) :=
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
  have dv_cache_0006 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0007 : y ∉ ((synCvv)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCun A (.cv y))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCun A B)).fv :=
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
  have dv_cache_0010 : y ∉ ((synCun A B)).fv :=
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
  have p0000 := @gElex A V
  have p0001 := @gElex B W
  have p0002 := @gUnexg A B (synCvv) (synCvv)
  have p0003 := @gUneq1 (.cv x) A (.cv y)
  have p0004 := @gUneq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCup x y
      dv_cache_0001
  have p0006 :=
    @gOvmpt2g x y A B (synCvv) (synCvv) (synCun (.cv x) (.cv y)) (synCun A B)
      (synCcup) (synCun A (.cv y)) (synCvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @gMpd3an3 (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCun A B) (synCvv)) (.classEq (synCo A (synCcup) B) (synCun A B))
      p0002 p0006
  have p0008 :=
    @gSyl2an (.classMem A V) (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classEq (synCo A (synCcup) B) (synCun A B)) (.classMem B W) p0000 p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fncup`. -/
@[expose]
noncomputable def gFncup : Nominal.NPrf (synWfn (synCcup) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCup x y
      dv_cache_0001
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gUnex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @gFnmpt2i x y (synCvv) (synCvv) (synCun (.cv x) (.cv y)) (synCcup) dv_cache_0002
      dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @gXpvv
  have p0006 := @gFneq2i (synCxp (synCvv) (synCvv)) (synCvv) (synCcup) p0005
  have p0007 :=
    @gMpbi (synWfn (synCcup) (synCxp (synCvv) (synCvv)))
      (synWfn (synCcup) (synCvv)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_brcupg`. -/
@[expose]
noncomputable def gBrcupg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (synWbr (synCop A B) (synCcup) C) (.classEq C (synCun A B)))) :=
  by
  have p0000 := @gFncup
  have p0001 := @gOpexg A B V W
  have p0002 := @gFnbrfvb (synCvv) (synCop A B) C (synCcup)
  have p0003 :=
    @gSylancr (synWa (.classMem A V) (.classMem B W)) (synWfn (synCcup) (synCvv))
      (.classMem (synCop A B) (synCvv))
      (synWb (.classEq (synCfv (synCcup) (synCop A B)) C)
        (synWbr (synCop A B) (synCcup) C))
      p0000 p0001 p0002
  have p0004 := @gCupvalg A B V W
  have p0005 :=
    @gEqeq1d (synWa (.classMem A V) (.classMem B W)) (synCo A (synCcup) B)
      (synCun A B) C p0004
  have p0006 := (Nominal.classEqRefl (synCo A (synCcup) B))
  have p0007 :=
    @gEqeq1i (synCo A (synCcup) B) (synCfv (synCcup) (synCop A B)) C p0006
  have p0008 := @gEqcom (synCun A B) C
  have p0009 :=
    @gN3bitr3g (synWa (.classMem A V) (.classMem B W))
      (.classEq (synCo A (synCcup) B) C) (.classEq (synCun A B) C)
      (.classEq (synCfv (synCcup) (synCop A B)) C) (.classEq C (synCun A B)) p0005
      p0007 p0008
  have p0010 :=
    @gBitr3d (synWa (.classMem A V) (.classMem B W))
      (.classEq (synCfv (synCcup) (synCop A B)) C) (synWbr (synCop A B) (synCcup) C)
      (.classEq C (synCun A B)) p0003 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_brcup`. -/
@[expose]
noncomputable def gBrcup (A : Class) (B : Class) (C : Class)
    (hyp_brcup_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brcup_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCop A B) (synCcup) C) (.classEq C (synCun A B))) :=
  by
  have p0000 := @gBrcupg A B C (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (synWbr (synCop A B) (synCcup) C) (.classEq C (synCun A B))) hyp_brcup_1
      hyp_brcup_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cupex`. -/
@[expose]
noncomputable def gCupex : Nominal.NPrf (.classMem (synCcup) (synCvv)) :=
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
  have dv_cache_0002 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0003 : y ∉ ((synCvv)).fv :=
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
    x ∉ ((synCun (synCins3 (synCsset)) (synCins2 (synCsset)))).fv :=
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
    y ∉ ((synCun (synCins3 (synCsset)) (synCins2 (synCsset)))).fv :=
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
    z ∉ ((synCun (synCins3 (synCsset)) (synCins2 (synCsset)))).fv :=
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
  have dv_cache_0007 : z ∉ ((synCun (.cv x) (.cv y))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCup x y
      dv_cache_0001
  have p0001 := @gVex y
  have p0002 := @gOtelins3 (synCsn (.cv z)) (.cv x) (.cv y) (synCsset) p0001
  have p0003 := @gVex z
  have p0004 := @gVex x
  have p0005 := @gOpelssetsn (.cv z) (.cv x) p0003 p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x) p0002
      p0006_e01_recanon
  have p0007 := @gOtelins2 (synCsn (.cv z)) (.cv x) (.cv y) (synCsset) p0004
  have p0008 := @gOpelssetsn (.cv z) (.cv y) p0003 p0001
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv y)) (synCsset)) (.objMem z y) p0007
      p0009_e01_recanon
  have p0010 :=
    @gOrbi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset)))
      (.objMem z x)
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.objMem z y) p0006 p0009
  have p0011 :=
    @gElun (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset))
      (synCins2 (synCsset))
  have p0012 := @gElun (.cv z) (.cv x) (.cv y)
  have p0013_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCun (.cv x) (.cv y)))
        (synWo (.objMem z x) (.objMem z y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synWo
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
    @gN3bitr4i
      (synWo (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
          (synCins3 (synCsset)))
        (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
          (synCins2 (synCsset))))
      (synWo (.objMem z x) (.objMem z y))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
        (synCun (synCins3 (synCsset)) (synCins2 (synCsset))))
      (.classMem (.cv z) (synCun (.cv x) (.cv y))) p0010 p0011 p0013_e02_recanon
  have p0014 :=
    @gReleqmpt2 x y z (synCvv) (synCvv)
      (synCun (synCins3 (synCsset)) (synCins2 (synCsset))) (synCun (.cv x) (.cv y))
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 p0013
  have p0015 :=
    @gEqtr4i (synCcup) (synCmpt2 x (synCvv) y (synCvv) (synCun (.cv x) (.cv y)))
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCun (synCins3 (synCsset)) (synCins2 (synCsset))))) (synC1c)))
      p0000 p0014
  have p0016 := @gVvex
  have p0018 := @gSsetex
  have p0019 := @gIns3ex (synCsset) p0018
  have p0021 := @gIns2ex (synCsset) p0018
  have p0022 := @gUnex (synCins3 (synCsset)) (synCins2 (synCsset)) p0019 p0021
  have p0023 :=
    @gMpt2exlem (synCvv) (synCvv)
      (synCun (synCins3 (synCsset)) (synCins2 (synCsset))) p0016 p0016 p0022
  have p0024 :=
    @gEqeltri (synCcup)
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset))
            (synCins3 (synCun (synCins3 (synCsset)) (synCins2 (synCsset))))) (synC1c)))
      (synCvv) p0015 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_composevalg`. -/
@[expose]
noncomputable def gComposevalg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (.classEq (synCo A (synCcompose) B) (synCcom A B))) :=
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
  have dv_cache_0006 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0007 : y ∉ ((synCvv)).fv :=
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
  have dv_cache_0008 : x ∉ ((synCcom A (.cv y))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCcom A B)).fv :=
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
  have dv_cache_0010 : y ∉ ((synCcom A B)).fv :=
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
  have p0000 := @gElex A V
  have p0001 := @gAdantr (.classMem A V) (.classMem A (synCvv)) (.classMem B W) p0000
  have p0002 := @gElex B W
  have p0003 := @gAdantl (.classMem B W) (.classMem B (synCvv)) (.classMem A V) p0002
  have p0004 := @gCoexg A B V W
  have p0005 := @gCoeq1 (.cv x) A (.cv y)
  have p0006 := @gCoeq2 (.cv y) B A
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCompose x y
      dv_cache_0001
  have p0008 :=
    @gOvmpt2g x y A B (synCvv) (synCvv) (synCcom (.cv x) (.cv y)) (synCcom A B)
      (synCcompose) (synCcom A (.cv y)) (synCvv) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0001 p0005 p0006 p0007
  have p0009 :=
    @gSyl3anc (synWa (.classMem A V) (.classMem B W)) (.classMem A (synCvv))
      (.classMem B (synCvv)) (.classMem (synCcom A B) (synCvv))
      (.classEq (synCo A (synCcompose) B) (synCcom A B)) p0001 p0003 p0004 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_composefn`. -/
@[expose]
noncomputable def gComposefn : Nominal.NPrf (synWfn (synCcompose) (synCvv)) :=
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
  have dv_cache_0001 : z ∉ ((synCcom (.cv x) (.cv y))).fv := by
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
    z ∉ ((synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))).fv :=
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
  have dv_cache_0006 : z ∉ ((synCvv)).fv :=
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
  have dv_cache_0007 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0008 : y ∉ ((synCvv)).fv :=
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
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 := @gCoex (.cv x) (.cv y) p0000 p0001
  have p0003 := @gEueq1 z (synCcom (.cv x) (.cv y)) dv_cache_0001 p0002
  have p0004 :=
    @gA1i (synWeu z (.classEq (.cv z) (synCcom (.cv x) (.cv y))))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))) p0003
  have p0005 :=
    @gFnoprab (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
      (.classEq (.cv z) (synCcom (.cv x) (.cv y))) x y z dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCompose x y
      dv_cache_0003
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt2 x y z (synCvv)
      (synCvv) (synCcom (.cv x) (.cv y)) dv_cache_0006 dv_cache_0006 dv_cache_0001
      dv_cache_0004 dv_cache_0005
  have p0008 :=
    @gEqtri (synCcompose) (synCmpt2 x (synCvv) y (synCvv) (synCcom (.cv x) (.cv y)))
      (synCoprab x y z
        (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
          (.classEq (.cv z) (synCcom (.cv x) (.cv y)))))
      p0006 p0007
  have p0009 := @gXpvv
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y (synCvv)
      (synCvv) dv_cache_0007 dv_cache_0008 dv_cache_0007 dv_cache_0008 dv_cache_0003
  have p0011 :=
    @gEqtr3i (synCxp (synCvv) (synCvv)) (synCvv)
      (synCopab x y (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      p0009 p0010
  have p0012 :=
    @gFneq1 (synCvv) (synCcompose)
      (synCoprab x y z
        (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
          (.classEq (.cv z) (synCcom (.cv x) (.cv y)))))
  have p0013 :=
    @gFneq2 (synCvv)
      (synCopab x y (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      (synCoprab x y z
        (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
          (.classEq (.cv z) (synCcom (.cv x) (.cv y)))))
  have p0014 :=
    @gSylan9bb
      (.classEq (synCcompose) (synCoprab x y z
          (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
            (.classEq (.cv z) (synCcom (.cv x) (.cv y))))))
      (synWfn (synCcompose) (synCvv))
      (synWfn (synCoprab x y z
          (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
            (.classEq (.cv z) (synCcom (.cv x) (.cv y))))) (synCvv))
      (.classEq (synCvv) (synCopab x y
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (synWfn (synCoprab x y z
          (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
            (.classEq (.cv z) (synCcom (.cv x) (.cv y))))) (synCopab x y
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      p0012 p0013
  have p0015 :=
    @gMp2an
      (.classEq (synCcompose) (synCoprab x y z
          (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
            (.classEq (.cv z) (synCcom (.cv x) (.cv y))))))
      (.classEq (synCvv) (synCopab x y
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      (synWb (synWfn (synCcompose) (synCvv)) (synWfn (synCoprab x y z
            (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
              (.classEq (.cv z) (synCcom (.cv x) (.cv y))))) (synCopab x y
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      p0008 p0011 p0014
  have p0016 :=
    @gMpbir (synWfn (synCcompose) (synCvv))
      (synWfn (synCoprab x y z
          (synWa (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
            (.classEq (.cv z) (synCcom (.cv x) (.cv y))))) (synCopab x y
          (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))))
      p0005 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_brcomposeg`. -/
@[expose]
noncomputable def gBrcomposeg (A : Class) (B : Class) (C : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (synWbr (synCop A B) (synCcompose) C) (.classEq (synCcom A B) C))) :=
  by
  have p0000 := @gComposefn
  have p0001 := @gOpexg A B V W
  have p0002 := @gFnbrfvb (synCvv) (synCop A B) C (synCcompose)
  have p0003 :=
    @gSylancr (synWa (.classMem A V) (.classMem B W)) (synWfn (synCcompose) (synCvv))
      (.classMem (synCop A B) (synCvv))
      (synWb (.classEq (synCfv (synCcompose) (synCop A B)) C)
        (synWbr (synCop A B) (synCcompose) C))
      p0000 p0001 p0002
  have p0004 := (Nominal.classEqRefl (synCo A (synCcompose) B))
  have p0005 := @gComposevalg A B V W
  have p0006 :=
    @gSyl5eqr (synWa (.classMem A V) (.classMem B W))
      (synCfv (synCcompose) (synCop A B)) (synCo A (synCcompose) B) (synCcom A B)
      p0004 p0005
  have p0007 :=
    @gEqeq1d (synWa (.classMem A V) (.classMem B W))
      (synCfv (synCcompose) (synCop A B)) (synCcom A B) C p0006
  have p0008 :=
    @gBitr3d (synWa (.classMem A V) (.classMem B W))
      (.classEq (synCfv (synCcompose) (synCop A B)) C)
      (synWbr (synCop A B) (synCcompose) C) (.classEq (synCcom A B) C) p0003 p0007
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

/-- Checked nominal proof certificate identified upstream as `g_composeex`. -/
@[expose]
noncomputable def gComposeex : Nominal.NPrf (.classMem (synCcompose) (synCvv)) :=
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
  have dv_cache_0013 : w ∉ ((synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))).fv :=
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
      ((synCima (synCin (synCins4 (synCsi3
                (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                  (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
              (synC1c))) (synC1c))).fv :=
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
      ((synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))).fv :=
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
      ((synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
              (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                (synC1c))) (synC1c)))).fv :=
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
      ((synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))).fv :=
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
      ((synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
          (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
            (synC1c)))).fv :=
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
  have dv_cache_0019 : t ∉ ((synCop (.cv w) (.cv u))).fv :=
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
      ((synCop (synCsn (.cv u)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))).fv :=
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
      ((synCin (synCins4 (synCsi3 (synCswap)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))).fv :=
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
  have dv_cache_0022 : v ∉ ((synCop (.cv u) (.cv t))).fv :=
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
      ((synCop (synCsn (.cv u)) (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
              (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))).fv :=
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
      ((synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))).fv :=
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
  have dv_cache_0026 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0027 : y ∉ ((synCvv)).fv :=
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
      ((synCima (synCima (synCin (synCins4 (synCsi3
                  (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                    (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                  (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                    (synC1c))) (synC1c))) (synC1c)) (synC1c))).fv :=
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
      ((synCima (synCima (synCin (synCins4 (synCsi3
                  (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                    (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                  (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                    (synC1c))) (synC1c))) (synC1c)) (synC1c))).fv :=
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
      ((synCima (synCima (synCin (synCins4 (synCsi3
                  (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                    (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                  (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                    (synC1c))) (synC1c))) (synC1c)) (synC1c))).fv :=
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
  have dv_cache_0031 : z ∉ ((synCcom (.cv x) (.cv y))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCompose x y
      dv_cache_0001
  have p0001 :=
    @gElopab
      (synWex u (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))))
      w t (.cv z) dv_cache_0002 dv_cache_0003
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo w t u (.cv x)
      (.cv y) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0003 :=
    @gEleq2i (synCcom (.cv x) (.cv y))
      (synCopab w t (synWex u
          (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t)))))
      (.cv z) p0002
  have p0004 :=
    @gElima1c w (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
      (synCima (synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
              (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                (synC1c))) (synC1c))) (synC1c))
      dv_cache_0013 dv_cache_0014
  have p0005 :=
    @gElima1c t
      (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
              (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                (synCin (synCins4 (synCsi3 (synCswap)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
              (synC1c))) (synC1c)))
      dv_cache_0015 dv_cache_0016
  have p0006 :=
    @gElin
      (synCop (synCsn (.cv t))
        (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
      (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
            (synCins2 (synCcnv (synC2nd))))))
      (synCima (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
          (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
            (synC1c))) (synC1c))
  have p0007 := @gVex x
  have p0008 := @gVex y
  have p0009 := @gOpex (.cv x) (.cv y) p0007 p0008
  have p0010 :=
    @gOqelins4 (synCsn (.cv t)) (synCsn (.cv w)) (synCsn (.cv z))
      (synCop (.cv x) (.cv y))
      (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
          (synCins2 (synCcnv (synC2nd)))))
      p0009
  have p0011 := @gVex t
  have p0012 := @gVex w
  have p0013 := @gVex z
  have p0014 :=
    @gOtsnelsi3 (.cv t) (.cv w) (.cv z)
      (synCin (synCxp (synCvv) (synCcnv (synC1st))) (synCins2 (synCcnv (synC2nd))))
      p0011 p0012 p0013
  have p0015 :=
    @gElin (synCop (.cv t) (synCop (.cv w) (.cv z)))
      (synCxp (synCvv) (synCcnv (synC1st))) (synCins2 (synCcnv (synC2nd)))
  have p0016 :=
    @gOpelxp (.cv t) (synCop (.cv w) (.cv z)) (synCvv) (synCcnv (synC1st))
  have p0017 :=
    @gMpbiran
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
        (synCxp (synCvv) (synCcnv (synC1st))))
      (.classMem (.cv t) (synCvv))
      (.classMem (synCop (.cv w) (.cv z)) (synCcnv (synC1st))) p0011 p0016
  have p0018 := (Nominal.biimpRefl (synWbr (.cv w) (synCcnv (synC1st)) (.cv z)))
  have p0019 := @gBrcnv (.cv w) (.cv z) (synC1st)
  have p0020 :=
    @gN3bitr2i
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
        (synCxp (synCvv) (synCcnv (synC1st))))
      (.classMem (synCop (.cv w) (.cv z)) (synCcnv (synC1st)))
      (synWbr (.cv w) (synCcnv (synC1st)) (.cv z)) (synWbr (.cv z) (synC1st) (.cv w))
      p0017 p0018 p0019
  have p0021 := @gOtelins2 (.cv t) (.cv w) (.cv z) (synCcnv (synC2nd)) p0012
  have p0022 := (Nominal.biimpRefl (synWbr (.cv t) (synCcnv (synC2nd)) (.cv z)))
  have p0023 := @gBrcnv (.cv t) (.cv z) (synC2nd)
  have p0024 :=
    @gN3bitr2i
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z))) (synCins2 (synCcnv (synC2nd))))
      (.classMem (synCop (.cv t) (.cv z)) (synCcnv (synC2nd)))
      (synWbr (.cv t) (synCcnv (synC2nd)) (.cv z)) (synWbr (.cv z) (synC2nd) (.cv t))
      p0021 p0022 p0023
  have p0025 :=
    @gAnbi12i
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
        (synCxp (synCvv) (synCcnv (synC1st))))
      (synWbr (.cv z) (synC1st) (.cv w))
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z))) (synCins2 (synCcnv (synC2nd))))
      (synWbr (.cv z) (synC2nd) (.cv t)) p0020 p0024
  have p0026 := @gOp1st2nd (.cv w) (.cv t) (.cv z) p0012 p0011
  have p0027 :=
    @gN3bitri
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
        (synCin (synCxp (synCvv) (synCcnv (synC1st))) (synCins2 (synCcnv (synC2nd)))))
      (synWa (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
          (synCxp (synCvv) (synCcnv (synC1st))))
        (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
          (synCins2 (synCcnv (synC2nd)))))
      (synWa (synWbr (.cv z) (synC1st) (.cv w)) (synWbr (.cv z) (synC2nd) (.cv t)))
      (.classEq (.cv z) (synCop (.cv w) (.cv t))) p0015 p0025 p0026
  have p0028 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCins4 (synCsi3
            (synCin (synCxp (synCvv) (synCcnv (synC1st)))
              (synCins2 (synCcnv (synC2nd)))))))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w)) (synCsn (.cv z))))
        (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
            (synCins2 (synCcnv (synC2nd))))))
      (.classMem (synCop (.cv t) (synCop (.cv w) (.cv z)))
        (synCin (synCxp (synCvv) (synCcnv (synC1st))) (synCins2 (synCcnv (synC2nd)))))
      (.classEq (.cv z) (synCop (.cv w) (.cv t))) p0010 p0014 p0027
  have p0029 :=
    @gElima1c u
      (synCop (synCsn (.cv t))
        (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
      (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))) (synCima
          (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
      dv_cache_0017 dv_cache_0018
  have p0030 :=
    @gElin
      (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
      (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
      (synCima (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c))
  have p0031 := @gSnex (.cv t)
  have p0032 :=
    @gOtelins2 (synCsn (.cv u)) (synCsn (.cv t))
      (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCima (synCin (synCins4 (synCsi3 (synCswap)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))
      p0031
  have p0033 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t
      (synCop (.cv w) (.cv u)) (.cv y) dv_cache_0019 dv_cache_0008)
  have p0034 := (Nominal.biimpRefl (synWbr (.cv w) (.cv y) (.cv u)))
  have p0035 :=
    @gElima1c t
      (synCop (synCsn (.cv u))
        (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
      (synCin (synCins4 (synCsi3 (synCswap)))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))
      dv_cache_0020 dv_cache_0021
  have p0036 :=
    @gElin
      (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
      (synCins4 (synCsi3 (synCswap)))
      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))
  have p0037 := @gSnex (.cv z)
  have p0038 := @gOpex (synCsn (.cv z)) (synCop (.cv x) (.cv y)) p0037 p0009
  have p0039 :=
    @gOqelins4 (synCsn (.cv t)) (synCsn (.cv u)) (synCsn (.cv w))
      (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCsi3 (synCswap)) p0038
  have p0040 := @gVex u
  have p0041 := @gOtsnelsi3 (.cv t) (.cv u) (.cv w) (synCswap) p0011 p0040 p0012
  have p0042 :=
    (Nominal.biimpRefl (synWbr (.cv t) (synCswap) (synCop (.cv u) (.cv w))))
  have p0043 := @gBrswap2 (.cv t) (.cv u) (.cv w) p0040 p0012
  have p0044 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u)) (synCsn (.cv w))))
        (synCsi3 (synCswap)))
      (.classMem (synCop (.cv t) (synCop (.cv u) (.cv w))) (synCswap))
      (synWbr (.cv t) (synCswap) (synCop (.cv u) (.cv w)))
      (.classEq (.cv t) (synCop (.cv w) (.cv u))) p0041 p0042 p0043
  have p0045 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins4 (synCsi3 (synCswap))))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u)) (synCsn (.cv w))))
        (synCsi3 (synCswap)))
      (.classEq (.cv t) (synCop (.cv w) (.cv u))) p0039 p0044
  have p0046 := @gSnex (.cv u)
  have p0047 :=
    @gOtelins2 (synCsn (.cv t)) (synCsn (.cv u))
      (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCins2 (synCins2 (synCins2 (synCsset)))) p0046
  have p0048 := @gSnex (.cv w)
  have p0049 :=
    @gOtelins2 (synCsn (.cv t)) (synCsn (.cv w))
      (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
      (synCins2 (synCins2 (synCsset))) p0048
  have p0050 :=
    @gOtelins2 (synCsn (.cv t)) (synCsn (.cv z)) (synCop (.cv x) (.cv y))
      (synCins2 (synCsset)) p0037
  have p0051 := @gOtelins2 (synCsn (.cv t)) (.cv x) (.cv y) (synCsset) p0007
  have p0052 := @gOpelssetsn (.cv t) (.cv y) p0011 p0008
  have p0053_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv t)) (.cv y)) (synCsset)) (.objMem t y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv t)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv t)) (synCop (.cv x) (.cv y))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv t)) (.cv y)) (synCsset)) (.objMem t y) p0050
      p0051 p0053_e02_recanon
  have p0054 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
        (synCins2 (synCins2 (synCins2 (synCsset)))))
      (.classMem
        (synCop (synCsn (.cv t)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem t y) p0047 p0049 p0053
  have p0055 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins4 (synCsi3 (synCswap))))
      (.classEq (.cv t) (synCop (.cv w) (.cv u)))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))
      (.objMem t y) p0045 p0054
  have p0056 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCin (synCins4 (synCsi3 (synCswap)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))))
      (synWa (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
              (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
          (synCins4 (synCsi3 (synCswap)))) (.classMem (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv u)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))))
      (synWa (.classEq (.cv t) (synCop (.cv w) (.cv u))) (.objMem t y)) p0036 p0055
  have p0057 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCin (synCins4 (synCsi3 (synCswap)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))))
      (synWa (.classEq (.cv t) (synCop (.cv w) (.cv u))) (.objMem t y)) t p0056
  have p0058 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
      (synWex t (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv u))
              (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
          (synCin (synCins4 (synCsi3 (synCswap)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))))
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv w) (.cv u))) (.objMem t y)))
      p0035 p0057
  have p0059_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv w) (.cv u)) (.cv y)) (synWex t
          (synWa (.classEq (.cv t) (synCop (.cv w) (.cv u))) (.objMem t y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gN3bitr4ri (.classMem (synCop (.cv w) (.cv u)) (.cv y))
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv w) (.cv u))) (.objMem t y)))
      (synWbr (.cv w) (.cv y) (.cv u))
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
      p0059_e00_recanon p0034 p0058
  have p0060 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))))
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
      (synWbr (.cv w) (.cv y) (.cv u)) p0032 p0059
  have p0061 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV v
      (synCop (.cv u) (.cv t)) (.cv x) dv_cache_0022 dv_cache_0023)
  have p0062 := (Nominal.biimpRefl (synWbr (.cv u) (.cv x) (.cv t)))
  have p0063 :=
    @gElima1c v
      (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
      (synCin (synCins4 (synCsi3 (synCid)))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      dv_cache_0024 dv_cache_0025
  have p0064 :=
    @gElin
      (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
      (synCins4 (synCsi3 (synCid)))
      (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
  have p0065 :=
    @gOpex (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) p0048
      p0038
  have p0066 :=
    @gOqelins4 (synCsn (.cv v)) (synCsn (.cv u)) (synCsn (.cv t))
      (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCsi3 (synCid)) p0065
  have p0067 := @gVex v
  have p0068 := @gOtsnelsi3 (.cv v) (.cv u) (.cv t) (synCid) p0067 p0040 p0011
  have p0069 := (Nominal.biimpRefl (synWbr (.cv v) (synCid) (synCop (.cv u) (.cv t))))
  have p0070 := @gOpex (.cv u) (.cv t) p0040 p0011
  have p0071 := @gIdeq (.cv v) (synCop (.cv u) (.cv t)) p0070
  have p0072 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u)) (synCsn (.cv t))))
        (synCsi3 (synCid)))
      (.classMem (synCop (.cv v) (synCop (.cv u) (.cv t))) (synCid))
      (synWbr (.cv v) (synCid) (synCop (.cv u) (.cv t)))
      (.classEq (.cv v) (synCop (.cv u) (.cv t))) p0068 p0069 p0071
  have p0073 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
        (synCins4 (synCsi3 (synCid))))
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u)) (synCsn (.cv t))))
        (synCsi3 (synCid)))
      (.classEq (.cv v) (synCop (.cv u) (.cv t))) p0066 p0072
  have p0074 :=
    @gOtelins2 (synCsn (.cv v)) (synCsn (.cv u))
      (synCop (synCsn (.cv t))
        (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))) p0046
  have p0075 :=
    @gOtelins2 (synCsn (.cv v)) (synCsn (.cv t))
      (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
      (synCins2 (synCins2 (synCins3 (synCsset)))) p0031
  have p0076 :=
    @gOtelins2 (synCsn (.cv v)) (synCsn (.cv w))
      (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))
      (synCins2 (synCins3 (synCsset))) p0048
  have p0077 :=
    @gOtelins2 (synCsn (.cv v)) (synCsn (.cv z)) (synCop (.cv x) (.cv y))
      (synCins3 (synCsset)) p0037
  have p0078 := @gOtelins3 (synCsn (.cv v)) (.cv x) (.cv y) (synCsset) p0008
  have p0079 := @gOpelssetsn (.cv v) (.cv x) p0067 p0007
  have p0080_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv v)) (.cv x)) (synCsset)) (.objMem v x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
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
    @gBitri
      (.classMem (synCop (synCsn (.cv v)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv v)) (.cv x)) (synCsset)) (.objMem v x) p0078
      p0080_e01_recanon
  have p0081 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
        (synCins2 (synCins2 (synCins3 (synCsset)))))
      (.classMem
        (synCop (synCsn (.cv v)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCins2 (synCins3 (synCsset))))
      (.classMem (synCop (synCsn (.cv v)) (synCop (.cv x) (.cv y))) (synCins3 (synCsset)))
      (.objMem v x) p0076 p0077 p0080
  have p0082 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
        (synCins2 (synCins2 (synCins3 (synCsset)))))
      (.objMem v x) p0074 p0075 p0081
  have p0083 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
        (synCins4 (synCsi3 (synCid))))
      (.classEq (.cv v) (synCop (.cv u) (.cv t)))
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      (.objMem v x) p0073 p0082
  have p0084 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
        (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))))
      (synWa (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
              (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                  (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
          (synCins4 (synCsi3 (synCid)))) (.classMem (synCop (synCsn (.cv v))
            (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                  (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))))
      (synWa (.classEq (.cv v) (synCop (.cv u) (.cv t))) (.objMem v x)) p0064 p0083
  have p0085 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
            (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
        (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))))
      (synWa (.classEq (.cv v) (synCop (.cv u) (.cv t))) (.objMem v x)) v p0084
  have p0086 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
      (synWex v (.classMem (synCop (synCsn (.cv v)) (synCop (synCsn (.cv u))
              (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
                  (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))))
          (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))))
      (synWex v (synWa (.classEq (.cv v) (synCop (.cv u) (.cv t))) (.objMem v x)))
      p0063 p0085
  have p0087_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv u) (.cv t)) (.cv x)) (synWex v
          (synWa (.classEq (.cv v) (synCop (.cv u) (.cv t))) (.objMem v x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
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
    @gN3bitr4ri (.classMem (synCop (.cv u) (.cv t)) (.cv x))
      (synWex v (synWa (.classEq (.cv v) (synCop (.cv u) (.cv t))) (.objMem v x)))
      (synWbr (.cv u) (.cv x) (.cv t))
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
      p0087_e00_recanon p0062 p0086
  have p0088 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))))
      (synWbr (.cv w) (.cv y) (.cv u))
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
      (synWbr (.cv u) (.cv x) (.cv t)) p0060 p0087
  have p0089 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
          (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
            (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
              (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))) (synCins2 (synCima
              (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))))
        (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
              (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))) (synCima
            (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
            (synC1c))))
      (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))) p0030
      p0088
  have p0090 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))))
        (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
          (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
            (synC1c))))
      (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))) u p0089
  have p0091 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCima (synCin
            (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
              (synC1c))) (synC1c)))
      (synWex u (.classMem (synCop (synCsn (.cv u)) (synCop (synCsn (.cv t))
              (synCop (synCsn (.cv w))
                (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))) (synCin (synCins2
              (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
              (synC1c)))))
      (synWex u (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))))
      p0029 p0090
  have p0092 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCins4 (synCsi3
            (synCin (synCxp (synCvv) (synCcnv (synC1st)))
              (synCins2 (synCcnv (synC2nd)))))))
      (.classEq (.cv z) (synCop (.cv w) (.cv t)))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCima (synCin
            (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
              (synC1c))) (synC1c)))
      (synWex u (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))))
      p0028 p0091
  have p0093 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCin (synCins4
            (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
              (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                (synC1c))) (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
              (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCins4 (synCsi3
              (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                (synCins2 (synCcnv (synC2nd))))))) (.classMem (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))))
          (synCima (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
              (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                (synC1c))) (synC1c))))
      (synWa (.classEq (.cv z) (synCop (.cv w) (.cv t))) (synWex u
          (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t)))))
      p0006 p0092
  have p0094 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCin (synCins4
            (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
              (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                (synC1c))) (synC1c))))
      (synWa (.classEq (.cv z) (synCop (.cv w) (.cv t))) (synWex u
          (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t)))))
      t p0093
  have p0095 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCima (synCin (synCins4 (synCsi3
                (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                  (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
              (synC1c))) (synC1c)))
      (synWex t (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv w))
              (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))) (synCin (synCins4
              (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                  (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
              (synC1c)))))
      (synWex t (synWa (.classEq (.cv z) (synCop (.cv w) (.cv t))) (synWex u
            (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))))))
      p0005 p0094
  have p0096 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))))
        (synCima (synCin (synCins4 (synCsi3
                (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                  (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
              (synC1c))) (synC1c)))
      (synWex t (synWa (.classEq (.cv z) (synCop (.cv w) (.cv t))) (synWex u
            (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t))))))
      w p0095
  have p0097 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCima (synCima
            (synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                    (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                  (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                    (synC1c))) (synC1c))) (synC1c)) (synC1c)))
      (synWex w (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y)))) (synCima (synCin (synCins4
                (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                    (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                  (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                    (synC1c))) (synC1c))) (synC1c))))
      (synWex w (synWex t (synWa (.classEq (.cv z) (synCop (.cv w) (.cv t))) (synWex u
              (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t)))))))
      p0004 p0096
  have p0098 :=
    @gN3bitr4ri
      (.classMem (.cv z) (synCopab w t (synWex u (synWa (synWbr (.cv w) (.cv y) (.cv u))
              (synWbr (.cv u) (.cv x) (.cv t))))))
      (synWex w (synWex t (synWa (.classEq (.cv z) (synCop (.cv w) (.cv t))) (synWex u
              (synWa (synWbr (.cv w) (.cv y) (.cv u)) (synWbr (.cv u) (.cv x) (.cv t)))))))
      (.classMem (.cv z) (synCcom (.cv x) (.cv y)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv y))) (synCima (synCima
            (synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                    (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                  (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                        (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                    (synC1c))) (synC1c))) (synC1c)) (synC1c)))
      p0001 p0003 p0097
  have p0099 :=
    @gReleqmpt2 x y z (synCvv) (synCvv)
      (synCima (synCima (synCin (synCins4 (synCsi3
                (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                  (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
              (synC1c))) (synC1c)) (synC1c))
      (synCcom (.cv x) (.cv y)) dv_cache_0026 dv_cache_0027 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0001 dv_cache_0032
      dv_cache_0033 p0098
  have p0100 :=
    @gEqtr4i (synCcompose)
      (synCmpt2 x (synCvv) y (synCvv) (synCcom (.cv x) (.cv y)))
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCima (synCima (synCin
                    (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                          (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2
                          (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                              (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))
                            (synC1c))) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2
                                (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
                      (synC1c))) (synC1c)) (synC1c)))) (synC1c)))
      p0000 p0099
  have p0101 := @gVvex
  have p0104 := @gN1stex
  have p0105 := @gCnvex (synC1st) p0104
  have p0106 := @gXpex (synCvv) (synCcnv (synC1st)) p0101 p0105
  have p0107 := @gN2ndex
  have p0108 := @gCnvex (synC2nd) p0107
  have p0109 := @gIns2ex (synCcnv (synC2nd)) p0108
  have p0110 :=
    @gInex (synCxp (synCvv) (synCcnv (synC1st))) (synCins2 (synCcnv (synC2nd)))
      p0106 p0109
  have p0111 :=
    @gSi3ex
      (synCin (synCxp (synCvv) (synCcnv (synC1st))) (synCins2 (synCcnv (synC2nd))))
      p0110
  have p0112 :=
    @gIns4ex
      (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
          (synCins2 (synCcnv (synC2nd)))))
      p0111
  have p0113 := @gSwapex
  have p0114 := @gSi3ex (synCswap) p0113
  have p0115 := @gIns4ex (synCsi3 (synCswap)) p0114
  have p0116 := @gSsetex
  have p0117 := @gIns2ex (synCsset) p0116
  have p0118 := @gIns2ex (synCins2 (synCsset)) p0117
  have p0119 := @gIns2ex (synCins2 (synCins2 (synCsset))) p0118
  have p0120 := @gIns2ex (synCins2 (synCins2 (synCins2 (synCsset)))) p0119
  have p0121 :=
    @gInex (synCins4 (synCsi3 (synCswap)))
      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))) p0115 p0120
  have p0122 := @gN1cex
  have p0123 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCswap)))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))
      (synC1c) p0121 p0122
  have p0124 :=
    @gIns2ex
      (synCima (synCin (synCins4 (synCsi3 (synCswap)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))
      p0123
  have p0125 := @gIdex
  have p0126 := @gSi3ex (synCid) p0125
  have p0127 := @gIns4ex (synCsi3 (synCid)) p0126
  have p0129 := @gIns3ex (synCsset) p0116
  have p0130 := @gIns2ex (synCins3 (synCsset)) p0129
  have p0131 := @gIns2ex (synCins2 (synCins3 (synCsset))) p0130
  have p0132 := @gIns2ex (synCins2 (synCins2 (synCins3 (synCsset)))) p0131
  have p0133 :=
    @gIns2ex (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))) p0132
  have p0134 :=
    @gInex (synCins4 (synCsi3 (synCid)))
      (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))) p0127 p0133
  have p0136 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCid)))
        (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
      (synC1c) p0134 p0122
  have p0137 :=
    @gInex
      (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
      (synCima (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c))
      p0124 p0136
  have p0139 :=
    @gImaex
      (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c))) (synCima
          (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
      (synC1c) p0137 p0122
  have p0140 :=
    @gInex
      (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
            (synCins2 (synCcnv (synC2nd))))))
      (synCima (synCin (synCins2 (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
          (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
            (synC1c))) (synC1c))
      p0112 p0139
  have p0142 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
              (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                (synCin (synCins4 (synCsi3 (synCswap)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
              (synC1c))) (synC1c)))
      (synC1c) p0140 p0122
  have p0144 :=
    @gImaex
      (synCima (synCin (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
              (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCins2 (synCins3 (synCsset)))))))
                (synC1c))) (synC1c))) (synC1c))
      (synC1c) p0142 p0122
  have p0145 :=
    @gMpt2exlem (synCvv) (synCvv)
      (synCima (synCima (synCin (synCins4 (synCsi3
                (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                  (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2 (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCins2 (synCins2 (synCsset)))))) (synC1c)))
                (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2
                      (synCins2 (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
              (synC1c))) (synC1c)) (synC1c))
      p0101 p0101 p0144
  have p0146 :=
    @gEqeltri (synCcompose)
      (synCdif (synCxp (synCxp (synCvv) (synCvv)) (synCvv)) (synCima
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCima (synCima (synCin
                    (synCins4 (synCsi3 (synCin (synCxp (synCvv) (synCcnv (synC1st)))
                          (synCins2 (synCcnv (synC2nd)))))) (synCima (synCin (synCins2
                          (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                              (synCins2 (synCins2 (synCins2 (synCins2 (synCsset))))))
                            (synC1c))) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2
                                (synCins2 (synCins2 (synCins3 (synCsset))))))) (synC1c)))
                      (synC1c))) (synC1c)) (synC1c)))) (synC1c)))
      (synCvv) p0100 p0145
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

/-- Checked nominal proof certificate identified upstream as `g_brdisjg`. -/
@[expose]
noncomputable def gBrdisjg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (synWbr A (synCdisj) B) (.classEq (synCin A B) (synC0)))) :=
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
  have dv_cache_0006 : x ∉ ((Wff.classEq (synCin A B) (synC0))).fv :=
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
  have dv_cache_0007 : y ∉ ((Wff.classEq (synCin A B) (synC0))).fv :=
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
  have p0000 := @gIneq1 (.cv x) A (.cv y)
  have p0001 :=
    @gEqeq1d (.classEq (.cv x) A) (synCin (.cv x) (.cv y)) (synCin A (.cv y)) (synC0)
      p0000
  have p0002 := @gIneq2 (.cv y) B A
  have p0003 :=
    @gEqeq1d (.classEq (.cv y) B) (synCin A (.cv y)) (synCin A B) (synC0) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfDisj x y
      dv_cache_0001
  have p0005 :=
    @gBrabg (.classEq (synCin (.cv x) (.cv y)) (synC0))
      (.classEq (synCin A (.cv y)) (synC0)) (.classEq (synCin A B) (synC0)) x y A B V
      W (synCdisj) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0001 p0003 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
