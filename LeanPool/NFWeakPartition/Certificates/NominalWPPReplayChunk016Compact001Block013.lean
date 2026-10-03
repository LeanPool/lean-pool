/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part056`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppcardt4fnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cncs))
        (.classEq (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardt4fn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn (syn_csn (syn_csn D)))) (syn_cwppcardt4fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))) p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
          (syn_csn (syn_csn (syn_csn (syn_csn D))))))
      (.classMem D (syn_cncs)) p0001
  have p0003 := @g_wppcardt2fnmapndv
  have p0004 := @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs))
      (syn_csi (syn_cwppcardt2fn))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem D (syn_cncs)) p0007
  have p0009 := @g_snelpw1 D (syn_cncs)
  have p0010 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs))
      p0009
  have p0011 := @g_snelpw1 (syn_csn D) (syn_cpw1 (syn_cncs))
  have p0012 :=
    @g_biimpri (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) p0011
  have p0013 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0010 p0012
  have p0014 := @g_snelpw1 (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0015 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0014
  have p0016 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0013 p0015
  have p0017 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0018 :=
    @g_biimpri
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      p0017
  have p0019 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0016 p0018
  have p0020 :=
    @g_jca (.classMem D (syn_cncs))
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      p0008 p0019
  have p0021 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_csn (syn_csn (syn_csn (syn_csn D))))
      (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn)))
  have p0022 :=
    @g_syl (.classMem D (syn_cncs))
      (syn_wa (syn_wf (syn_csi (syn_csi (syn_cwppcardt2fn)))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
          (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn D))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (.classEq (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
          (syn_csn (syn_csn (syn_csn (syn_csn D))))) (syn_cfv (syn_cwppcardt2fn)
          (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn)))
            (syn_csn (syn_csn (syn_csn (syn_csn D)))))))
      p0020 p0021
  have p0034 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs))
      (syn_csn (syn_csn (syn_csn D))) (syn_csi (syn_cwppcardt2fn)) p0005
  have p0035 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_csn D))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (.classEq (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn)))
          (syn_csn (syn_csn (syn_csn (syn_csn D)))))
        (syn_csn (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D))))))
      p0016 p0034
  have p0042 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_csn (syn_csn D))
      (syn_cwppcardt2fn) p0003
  have p0043 :=
    @g_syl (.classMem D (syn_cncs))
      (.classMem (syn_csn (syn_csn D)) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      (.classEq (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D))))
        (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))))
      p0013 p0042
  have p0044 :=
    @g_sneqd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D))))
      (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))) p0043
  have p0045 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_csn (syn_cfv (syn_csi (syn_cwppcardt2fn)) (syn_csn (syn_csn (syn_csn D)))))
      (syn_csn (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))))) p0035 p0044
  have p0046 := @g_wppcardt2fnvalsingndv D
  have p0047 :=
    @g_sneqd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))
      (syn_ctc (syn_ctc D)) p0046
  have p0048 :=
    @g_sneqd (.classMem D (syn_cncs))
      (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D))))
      (syn_csn (syn_ctc (syn_ctc D))) p0047
  have p0049 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_csn (syn_csn (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn D)))))
      (syn_csn (syn_csn (syn_ctc (syn_ctc D)))) p0045 p0048
  have p0050 :=
    @g_fveq2d (.classMem D (syn_cncs))
      (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn))) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_csn (syn_csn (syn_ctc (syn_ctc D)))) (syn_cwppcardt2fn) p0049
  have p0051 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
        (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_cfv (syn_cwppcardt2fn) (syn_cfv (syn_csi (syn_csi (syn_cwppcardt2fn)))
          (syn_csn (syn_csn (syn_csn (syn_csn D))))))
      (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc D))))) p0022 p0050
  have p0052 := @g_tccl D
  have p0053 := @g_tccl (syn_ctc D)
  have p0054 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc D) (syn_cncs))
      (.classMem (syn_ctc (syn_ctc D)) (syn_cncs)) p0052 p0053
  have p0055 := @g_wppcardt2fnvalsingndv (syn_ctc (syn_ctc D))
  have p0056 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_ctc (syn_ctc D)) (syn_cncs))
      (.classEq (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc D)))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))
      p0054 p0055
  have p0057 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
        (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_cfv (syn_cwppcardt2fn) (syn_csn (syn_csn (syn_ctc (syn_ctc D)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) p0051 p0056
  have p0058 :=
    @g_eqtrd (.classMem D (syn_cncs))
      (syn_cfv (syn_cwppcardt4fn) (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_cfv (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
        (syn_csn (syn_csn (syn_csn (syn_csn D)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))) p0002 p0057
  exact p0058

@[expose]
noncomputable def g_cnv2resndv (A : Class) (B : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (syn_cin R (syn_cxp A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_not_R : x ∉ R.fv := by
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
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cin R (syn_cxp A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cin R (syn_cxp A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_brcnv (.cv x) (.cv y) (syn_cres (syn_ccnv (syn_cres R A)) B)
  have p0001 := @g_brres (.cv y) (.cv x) (syn_ccnv (syn_cres R A)) B
  have p0002 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y))
      (syn_wbr (.cv y) (syn_cres (syn_ccnv (syn_cres R A)) B) (.cv x))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_cres R A)) (.cv x)) (.classMem (.cv y) B))
      p0000 p0001
  have p0003 := @g_brcnv (.cv y) (.cv x) (syn_cres R A)
  have p0004 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_ccnv (syn_cres R A)) (.cv x))
      (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (.classMem (.cv y) B) p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_cres R A)) (.cv x)) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (.classMem (.cv y) B)) p0002 p0004
  have p0006 := @g_brres (.cv x) (.cv y) R A
  have p0007 :=
    @g_anbi1i (syn_wbr (.cv x) (syn_cres R A) (.cv y))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B)
      p0006
  have p0008 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y))
      (syn_wa (syn_wbr (.cv x) (syn_cres R A) (.cv y)) (.classMem (.cv y) B))
      (syn_wa (syn_wa (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B))
      p0005 p0007
  have p0009 :=
    @g_anass (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A) (.classMem (.cv y) B)
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y))
      (syn_wa (syn_wa (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      p0008 p0009
  have p0011 := @g_brxp (.cv x) (.cv y) A B
  have p0012 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cxp A B) (.cv y))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0011
  have p0013 :=
    @g_anbi2i (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (syn_wbr (.cv x) (syn_cxp A B) (.cv y)) (syn_wbr (.cv x) R (.cv y)) p0012
  have p0014 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y))) p0010
      p0013
  have p0015 := @g_brin (.cv x) (.cv y) R (syn_cxp A B)
  have p0016 :=
    @g_bicomi (syn_wbr (.cv x) (syn_cin R (syn_cxp A B)) (.cv y))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y))) p0015
  have p0017 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B)) (.cv y))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp A B) (.cv y)))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp A B)) (.cv y)) p0014 p0016
  have p0018 :=
    @g_eqbrriv x y (syn_ccnv (syn_cres (syn_ccnv (syn_cres R A)) B))
      (syn_cin R (syn_cxp A B)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0017
  exact p0018

@[expose]
noncomputable def g_cnvrngresndv (B : Class) (R : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cres (syn_ccnv R) B)) (syn_cin R (syn_cxp (syn_cvv) B))) :=
  by
  have dv_cache_0001 : Disjoint ((syn_cvv)).fv (R).fv := by
    exact
      (show Disjoint ((syn_cvv)).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact (show Disjoint ((∅ : Finset Var)) ((R).fv) from (by simp))))
  have p0000 := @g_resid R
  have p0001 := @g_cnveqi (syn_cres R (syn_cvv)) R p0000
  have p0002 := @g_reseq1i (syn_ccnv (syn_cres R (syn_cvv))) (syn_ccnv R) B p0001
  have p0003 :=
    @g_cnveqi (syn_cres (syn_ccnv (syn_cres R (syn_cvv))) B) (syn_cres (syn_ccnv R) B)
      p0002
  have p0004 := @g_cnv2resndv (syn_cvv) B R dv_cache_0001
  have p0005 :=
    @g_eqtr3i (syn_ccnv (syn_cres (syn_ccnv (syn_cres R (syn_cvv))) B))
      (syn_ccnv (syn_cres (syn_ccnv R) B)) (syn_cin R (syn_cxp (syn_cvv) B)) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_hwcodesunivndv :
    Nominal.NPrf (.classEq (syn_chwcodes (syn_cvv)) (syn_cwe)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcodes (syn_cvv)))
  have p0001 := @g_pwv
  have p0002 := @g_xpeq2i (syn_cpw (syn_cvv)) (syn_cvv) (syn_cvv) p0001
  have p0003 := @g_xpvv
  have p0004 :=
    @g_eqtri (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cxp (syn_cvv) (syn_cvv))
      (syn_cvv) p0002 p0003
  have p0005 :=
    @g_ineq2i (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cvv) (syn_cwe) p0004
  have p0006 := @g_inv1 (syn_cwe)
  have p0007 :=
    @g_eqtri (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))))
      (syn_cin (syn_cwe) (syn_cvv)) (syn_cwe) p0005 p0006
  have p0008 :=
    @g_eqtri (syn_chwcodes (syn_cvv))
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv)))) (syn_cwe) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_hwcnunivrrndv (A : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)))
        (syn_chwcn A)) :=
  by
  have p0000 := @g_cnvrngresndv (syn_cpw A) (syn_chwcn (syn_cvv))
  have p0001 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0002 :=
    @g_ineq1i (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cxp (syn_cvv) (syn_cpw A)) p0001
  have p0003 := (Nominal.classEqRefl (syn_chwcodes (syn_cvv)))
  have p0004 := @g_pwv
  have p0005 := @g_xpeq2i (syn_cpw (syn_cvv)) (syn_cvv) (syn_cvv) p0004
  have p0006 := @g_xpvv
  have p0007 :=
    @g_eqtri (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cxp (syn_cvv) (syn_cvv))
      (syn_cvv) p0005 p0006
  have p0008 :=
    @g_ineq2i (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))) (syn_cvv) (syn_cwe) p0007
  have p0009 := @g_inv1 (syn_cwe)
  have p0010 :=
    @g_eqtri (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv))))
      (syn_cin (syn_cwe) (syn_cvv)) (syn_cwe) p0008 p0009
  have p0011 :=
    @g_eqtri (syn_chwcodes (syn_cvv))
      (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw (syn_cvv)))) (syn_cwe) p0003 p0010
  have p0012 := @g_ineq1i (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_chwrels) p0011
  have p0013 :=
    @g_ineq1i (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cin (syn_cwe) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A)) p0012
  have p0014 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cin (syn_cwe) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A))) p0002
      p0013
  have p0015 := @g_in32 (syn_cwe) (syn_chwrels) (syn_cxp (syn_cvv) (syn_cpw A))
  have p0016 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cin (syn_cwe) (syn_chwrels)) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwrels)) p0014
      p0015
  have p0017 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0018 :=
    @g_eqcomi (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) p0017
  have p0019 :=
    @g_ineq1i (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwcodes A)
      (syn_chwrels) p0018
  have p0020 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwrels))
      (syn_cin (syn_chwcodes A) (syn_chwrels)) p0016 p0019
  have p0021 := (Nominal.classEqRefl (syn_chwcn A))
  have p0022 := @g_eqcomi (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) p0021
  have p0023 :=
    @g_eqtri (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A)))
      (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_chwcn A) p0020 p0022
  have p0024 :=
    @g_eqtri (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)))
      (syn_cin (syn_chwcn (syn_cvv)) (syn_cxp (syn_cvv) (syn_cpw A))) (syn_chwcn A) p0000
      p0023
  exact p0024

@[expose]
noncomputable def g_hwnisogendrrndv (A : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cres (syn_ccnv
              (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
            (syn_chwcn A))) (syn_chwniso A)) :=
  by
  have dv_cache_0001 :
    Disjoint ((syn_chwcn A)).fv
      ((syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))).fv :=
    by
    exact
      (show Disjoint ((syn_chwcn A)).fv
          ((syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show
              Disjoint ((A).fv)
                ((((syn_chwgen)).fv) ∪ (((syn_cxp (syn_chwbij) (syn_cvv))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((syn_chwgen)).fv) from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen];
                      exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))),
                  (show Disjoint ((A).fv) (((syn_cxp (syn_chwbij) (syn_cvv))).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp];
                      exact
                        (show Disjoint ((A).fv) ((((syn_chwbij)).fv) ∪ (((syn_cvv)).fv))
                          from
                          (Finset.disjoint_union_right.mpr
                            ⟨(show Disjoint ((A).fv) (((syn_chwbij)).fv) from
                                (by
                                  rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp)))),
                              (show Disjoint ((A).fv) (((syn_cvv)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp))))⟩))))⟩))))
  have p0000 :=
    @g_cnv2resndv (syn_chwcn A) (syn_chwcn A)
      (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) dv_cache_0001
  have p0001 := (Nominal.classEqRefl (syn_chwniso A))
  have p0002 :=
    @g_eqcomi (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      p0001
  have p0003 :=
    @g_eqtri
      (syn_ccnv (syn_cres (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_chwniso A) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_wpppowsetfnexndv :
    Nominal.NPrf (.classMem (syn_cwpppowsetfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0001 := @g_ssetex
  have p0002 := @g_cnvex (syn_csset) p0001
  have p0003 := @g_imageex (syn_ccnv (syn_csset)) p0002
  have p0004 :=
    @g_eqeltri (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_wpppowsetfnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) :=
  by
  have p0000 := @g_ssetex
  have p0001 := @g_cnvex (syn_csset) p0000
  have p0002 := @g_wppimagefn (syn_ccnv (syn_csset)) p0001
  have p0003 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_wpppowsetfnvalndv (A : Class)
    (hyp_wpppowsetfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpppowsetfn) (syn_csn A)) (syn_cpw A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ ((syn_csset)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
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
  have p0000 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0000
  have p0002 := @g_ssetex
  have p0003 := @g_cnvex (syn_csset) p0002
  have p0004 := @g_snex A
  have p0005 := @g_fvimagecl (syn_csn A) (syn_ccnv (syn_csset)) p0003 p0004
  have p0006 := @g_iniseg x (syn_csset) A dv_cache_0001 dv_cache_0002
  have p0007 := @g_vex x
  have p0008 := @g_brsset (.cv x) A p0007 hyp_wpppowsetfnvalndv_1
  have p0009 := @g_abbii (syn_wbr (.cv x) (syn_csset) A) (syn_wss (.cv x) A) x p0008
  have p0010 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_csset)) (syn_csn A))
      (.cab x (syn_wbr (.cv x) (syn_csset) A)) (.cab x (syn_wss (.cv x) A)) p0006 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x A dv_cache_0002
  have p0012 := @g_eqcomi (syn_cpw A) (.cab x (syn_wss (.cv x) A)) p0011
  have p0013 :=
    @g_eqtri (syn_cima (syn_ccnv (syn_csset)) (syn_csn A)) (.cab x (syn_wss (.cv x) A))
      (syn_cpw A) p0010 p0012
  have p0014 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_ccnv (syn_csset))) (syn_csn A))
      (syn_cima (syn_ccnv (syn_csset)) (syn_csn A)) (syn_cpw A) p0005 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwpppowsetfn) (syn_csn A))
      (syn_cfv (syn_cimage (syn_ccnv (syn_csset))) (syn_csn A)) (syn_cpw A) p0001 p0014
  exact p0015

@[expose]
noncomputable def g_wpphwcnsetfnvalndv (A : Class)
    (hyp_wpphwcnsetfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0000
  have p0002 := @g_lnimageresfnfn
  have p0003 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0004 := @g_hwcodesunivndv
  have p0005 := @g_weex
  have p0006 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0004 p0005
  have p0007 := @g_hwrelsex
  have p0008 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0006 p0007
  have p0009 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0003 p0008
  have p0010 := @g_cnvex (syn_chwcn (syn_cvv)) p0009
  have p0011 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_ssetex
  have p0014 := @g_cnvex (syn_csset) p0013
  have p0015 := @g_wppimagefn (syn_ccnv (syn_csset)) p0014
  have p0016 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0017 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0016
  have p0018 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0015 p0017
  have p0019 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0012 p0018
  have p0020 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_inidm (syn_cvv)
  have p0023 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0022
  have p0024 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0021 p0023
  have p0025 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0002 p0024
  have p0026 := @g_snex A
  have p0027 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))) (syn_cvv))
      (.classMem (syn_csn A) (syn_cvv)) p0025 p0026
  have p0028 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
  have p0029 := Nominal.mp p0027 p0028
  have p0053 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      (.classMem (syn_csn A) (syn_cvv)) p0024 p0026
  have p0054 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
  have p0055 := Nominal.mp p0053 p0054
  have p0073 :=
    @g_fvtxpvv (syn_csn A) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
      (syn_cwpppowsetfn) p0012 p0018 p0026
  have p0083 := @g_fvconst2 (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_csn A) p0010
  have p0084 := Nominal.mp p0026 p0083
  have p0085 := @g_wpppowsetfnvalndv A hyp_wpphwcnsetfnvalndv_1
  have p0086 :=
    @g_opeq12i
      (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_csn A))
      (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cfv (syn_cwpppowsetfn) (syn_csn A))
      (syn_cpw A) p0084 p0085
  have p0087 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_csn A))
      (syn_cop (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_csn A)) (syn_cfv (syn_cwpppowsetfn) (syn_csn A)))
      (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) p0073 p0086
  have p0088 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_csn A))
      (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) (syn_clnimageresfn) p0087
  have p0089 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))) (syn_csn A))
      (syn_cfv (syn_clnimageresfn) (syn_cfv
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn)) (syn_csn A)))
      (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)))
      p0055 p0088
  have p0098 := @g_pwex A hyp_wpphwcnsetfnvalndv_1
  have p0099 :=
    @g_lnimageresfnval (syn_cpw A) (syn_ccnv (syn_chwcn (syn_cvv))) p0010 p0098
  have p0100 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))) (syn_csn A))
      (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)))
      (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) p0089 p0099
  have p0101 :=
    @g_fveq2i
      (syn_cfv (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))) (syn_csn A))
      (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) (syn_cimage (syn_cswap))
      p0100
  have p0102 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_csn A))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn))) (syn_csn A)))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)))
      p0029 p0101
  have p0112 := @g_resex (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A) p0010 p0098
  have p0113 :=
    @g_wppimageswapfv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)) p0112
  have p0114 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_csn A))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A)))
      (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) p0102 p0113
  have p0115 := @g_hwcnunivrrndv A
  have p0116 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_csn A))
      (syn_ccnv (syn_cres (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cpw A))) (syn_chwcn A)
      p0114 p0115
  have p0117 :=
    @g_eqtri (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A))
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_csn A))
      (syn_chwcn A) p0001 p0116
  exact p0117

@[expose]
noncomputable def g_wpphwgendomfnvalndv (A : Class)
    (hyp_wpphwgendomfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpphwgendomfn) (syn_csn A))
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      p0000
  have p0002 := @g_hwgenex
  have p0003 := @g_hwbijex
  have p0004 := @g_vvex
  have p0005 := @g_xpex (syn_chwbij) (syn_cvv) p0003 p0004
  have p0006 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cvv)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_imageswapfn
  have p0010 := @g_lnimageresfnfn
  have p0011 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0012 := @g_hwcodesunivndv
  have p0013 := @g_weex
  have p0014 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0012 p0013
  have p0015 := @g_hwrelsex
  have p0016 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0014 p0015
  have p0017 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0011 p0016
  have p0018 := @g_cnvex (syn_chwcn (syn_cvv)) p0017
  have p0019 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @g_ssetex
  have p0022 := @g_cnvex (syn_csset) p0021
  have p0023 := @g_wppimagefn (syn_ccnv (syn_csset)) p0022
  have p0024 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0025 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0024
  have p0026 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0023 p0025
  have p0027 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0020 p0026
  have p0028 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @g_inidm (syn_cvv)
  have p0031 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0030
  have p0032 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0029 p0031
  have p0033 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0010 p0032
  have p0034 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0009 p0033
  have p0035 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0036 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0035
  have p0037 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_cvv))
      p0034 p0036
  have p0038 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0008 p0037
  have p0039 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)
  have p0040 := Nominal.mp p0038 p0039
  have p0042 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0030
  have p0043 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      p0040 p0042
  have p0044 := @g_snex A
  have p0045 :=
    @g_pm3_2i
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      (.classMem (syn_csn A) (syn_cvv)) p0043 p0044
  have p0046 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
  have p0047 := Nominal.mp p0045 p0046
  have p0085 :=
    @g_fvtxpvv (syn_csn A)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn) p0008 p0037 p0044
  have p0092 :=
    @g_fvconst2 (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_csn A) p0006
  have p0093 := Nominal.mp p0044 p0092
  have p0094 := @g_wpphwcnsetfnvalndv A hyp_wpphwgendomfnvalndv_1
  have p0095 :=
    @g_opeq12i
      (syn_cfv (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_csn A))
      (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A) p0093 p0094
  have p0096 :=
    @g_eqtri
      (syn_cfv (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_csn A))
      (syn_cop (syn_cfv (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_csn A))
        (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)))
      (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      p0085 p0095
  have p0097 :=
    @g_fveq2i
      (syn_cfv (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_csn A))
      (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      (syn_clnimageresfn) p0096
  have p0098 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_csn A))
      (syn_cfv (syn_clnimageresfn) (syn_cfv (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn)) (syn_csn A)))
      (syn_cfv (syn_clnimageresfn)
        (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      p0047 p0097
  have p0104 := @g_hwcnex A hyp_wpphwgendomfnvalndv_1
  have p0105 :=
    @g_lnimageresfnval (syn_chwcn A)
      (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) p0006 p0104
  have p0106 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_csn A))
      (syn_cfv (syn_clnimageresfn)
        (syn_cop (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      p0098 p0105
  have p0107 :=
    @g_eqtri (syn_cfv (syn_cwpphwgendomfn) (syn_csn A))
      (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_csn A))
      (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      p0001 p0106
  exact p0107


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part057`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wpphwgencnvfnvalndv (A : Class)
    (hyp_wpphwgencnvfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A)) (syn_ccnv
          (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphwgencnvfn))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwgencnvfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0000
  have p0002 := @g_lnimageresfnfn
  have p0003 := @g_hwgenex
  have p0004 := @g_hwbijex
  have p0005 := @g_vvex
  have p0006 := @g_xpex (syn_chwbij) (syn_cvv) p0004 p0005
  have p0007 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_imageswapfn
  have p0012 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0013 := @g_hwcodesunivndv
  have p0014 := @g_weex
  have p0015 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0013 p0014
  have p0016 := @g_hwrelsex
  have p0017 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0015 p0016
  have p0018 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0012 p0017
  have p0019 := @g_cnvex (syn_chwcn (syn_cvv)) p0018
  have p0020 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_ssetex
  have p0023 := @g_cnvex (syn_csset) p0022
  have p0024 := @g_wppimagefn (syn_ccnv (syn_csset)) p0023
  have p0025 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0025
  have p0027 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0021 p0027
  have p0029 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0030 := Nominal.mp p0028 p0029
  have p0031 := @g_inidm (syn_cvv)
  have p0032 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0031
  have p0033 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0030 p0032
  have p0034 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0002 p0033
  have p0035 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0010 p0034
  have p0036 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0037 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0036
  have p0038 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_cvv))
      p0035 p0037
  have p0039 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0009 p0038
  have p0040 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)
  have p0041 := Nominal.mp p0039 p0040
  have p0043 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0031
  have p0044 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      p0041 p0043
  have p0045 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0002 p0044
  have p0046 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0047 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      p0046
  have p0048 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_cvv))
      p0045 p0047
  have p0049 := @g_snex A
  have p0050 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv))
      p0048 p0049
  have p0051 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)
  have p0052 := Nominal.mp p0050 p0051
  have p0053 := @g_wpphwgendomfnvalndv A hyp_wpphwgencnvfnvalndv_1
  have p0054 :=
    @g_fveq2i (syn_cfv (syn_cwpphwgendomfn) (syn_csn A))
      (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      (syn_cimage (syn_cswap)) p0053
  have p0055 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_csn A))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_cwpphwgendomfn) (syn_csn A)))
      (syn_cfv (syn_cimage (syn_cswap))
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      p0052 p0054
  have p0061 := @g_hwcnex A hyp_wpphwgencnvfnvalndv_1
  have p0062 :=
    @g_resex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A) p0007
      p0061
  have p0063 :=
    @g_wppimageswapfv
      (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      p0062
  have p0064 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_csn A))
      (syn_cfv (syn_cimage (syn_cswap))
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      (syn_ccnv
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      p0055 p0063
  have p0065 :=
    @g_eqtri (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A))
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_csn A))
      (syn_ccnv
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      p0001 p0064
  exact p0065

@[expose]
noncomputable def g_wpphwnisosetfnvalndv (A : Class)
    (hyp_wpphwnisosetfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A)) (syn_chwniso A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphwnisosetfn))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwnisosetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))))
      p0000
  have p0002 := @g_lnimageresfnfn
  have p0003 := @g_imageswapfn
  have p0005 := @g_hwgenex
  have p0006 := @g_hwbijex
  have p0007 := @g_vvex
  have p0008 := @g_xpex (syn_chwbij) (syn_cvv) p0006 p0007
  have p0009 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0005 p0008
  have p0010 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cvv)
  have p0011 := Nominal.mp p0009 p0010
  have p0014 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0015 := @g_hwcodesunivndv
  have p0016 := @g_weex
  have p0017 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0015 p0016
  have p0018 := @g_hwrelsex
  have p0019 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0017 p0018
  have p0020 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0014 p0019
  have p0021 := @g_cnvex (syn_chwcn (syn_cvv)) p0020
  have p0022 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @g_ssetex
  have p0025 := @g_cnvex (syn_csset) p0024
  have p0026 := @g_wppimagefn (syn_ccnv (syn_csset)) p0025
  have p0027 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0026 p0028
  have p0030 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0023 p0029
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := @g_inidm (syn_cvv)
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0033
  have p0035 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0002 p0035
  have p0037 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0003 p0036
  have p0038 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0039 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0038
  have p0040 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_cvv))
      p0037 p0039
  have p0041 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0011 p0040
  have p0042 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)
  have p0043 := Nominal.mp p0041 p0042
  have p0045 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0033
  have p0046 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      p0043 p0045
  have p0047 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0002 p0046
  have p0048 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0049 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      p0048
  have p0050 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_cvv))
      p0047 p0049
  have p0051 := @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0003 p0050
  have p0052 := (Nominal.classEqRefl (syn_cwpphwgencnvfn))
  have p0053 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0052
  have p0054 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0051
      p0053
  have p0084 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0054 p0040
  have p0085 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0086 := Nominal.mp p0084 p0085
  have p0088 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0033
  have p0089 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0086 p0088
  have p0090 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
      p0002 p0089
  have p0091 := @g_snex A
  have p0092 :=
    @g_pm3_2i
      (syn_wfn
        (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
        (syn_cvv))
      (.classMem (syn_csn A) (syn_cvv)) p0090 p0091
  have p0093 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
  have p0094 := Nominal.mp p0092 p0093
  have p0183 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv))
      (.classMem (syn_csn A) (syn_cvv)) p0089 p0091
  have p0184 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_clnimageresfn)
      (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
  have p0185 := Nominal.mp p0183 p0184
  have p0268 :=
    @g_fvtxpvv (syn_csn A) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn) p0054 p0040 p0091
  have p0269 := @g_wpphwgencnvfnvalndv A hyp_wpphwnisosetfnvalndv_1
  have p0270 := @g_wpphwcnsetfnvalndv A hyp_wpphwnisosetfnvalndv_1
  have p0271 :=
    @g_opeq12i (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A))
      (syn_ccnv
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A) p0269 p0270
  have p0272 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_csn A))
      (syn_cop (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A))
        (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)))
      (syn_cop (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
            (syn_chwcn A))) (syn_chwcn A))
      p0268 p0271
  have p0273 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_csn A))
      (syn_cop (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
            (syn_chwcn A))) (syn_chwcn A))
      (syn_clnimageresfn) p0272
  have p0274 :=
    @g_eqtri
      (syn_cfv
        (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
        (syn_csn A))
      (syn_cfv (syn_clnimageresfn)
        (syn_cfv (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_csn A)))
      (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      p0185 p0273
  have p0280 := @g_hwcnex A hyp_wpphwnisosetfnvalndv_1
  have p0281 :=
    @g_resex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A) p0009
      p0280
  have p0282 :=
    @g_cnvex
      (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))
      p0281
  have p0284 :=
    @g_lnimageresfnval (syn_chwcn A)
      (syn_ccnv
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      p0282 p0280
  have p0285 :=
    @g_eqtri
      (syn_cfv
        (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
        (syn_csn A))
      (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
            (syn_chwcn A))) (syn_chwcn A))
      p0274 p0284
  have p0286 :=
    @g_fveq2i
      (syn_cfv
        (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
        (syn_csn A))
      (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
            (syn_chwcn A))) (syn_chwcn A))
      (syn_cimage (syn_cswap)) p0285
  have p0287 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) (syn_csn A)))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      p0094 p0286
  have p0297 :=
    @g_resex
      (syn_ccnv
        (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
      (syn_chwcn A) p0282 p0280
  have p0298 :=
    @g_wppimageswapfv
      (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
            (syn_chwcn A))) (syn_chwcn A))
      p0297
  have p0299 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A))
      (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      (syn_ccnv (syn_cres (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      p0287 p0298
  have p0300 := @g_hwnisogendrrndv A
  have p0301 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A))
      (syn_ccnv (syn_cres (syn_ccnv
            (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))
          (syn_chwcn A)))
      (syn_chwniso A) p0299 p0300
  have p0302 :=
    @g_eqtri (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A))
      (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A))
      (syn_chwniso A) p0001 p0301
  exact p0302

@[expose]
noncomputable def g_wpphnpairfnvalndv (A : Class)
    (hyp_wpphnpairfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpphnpairfn) (syn_csn A))
        (syn_cop (syn_chwniso A) (syn_chwcn A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphnpairfn))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphnpairfn)
      (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0000
  have p0002 := @g_imageswapfn
  have p0003 := @g_lnimageresfnfn
  have p0006 := @g_hwgenex
  have p0007 := @g_hwbijex
  have p0008 := @g_vvex
  have p0009 := @g_xpex (syn_chwbij) (syn_cvv) p0007 p0008
  have p0010 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0006 p0009
  have p0011 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0015 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0016 := @g_hwcodesunivndv
  have p0017 := @g_weex
  have p0018 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0016 p0017
  have p0019 := @g_hwrelsex
  have p0020 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0018 p0019
  have p0021 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0015 p0020
  have p0022 := @g_cnvex (syn_chwcn (syn_cvv)) p0021
  have p0023 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 := @g_ssetex
  have p0026 := @g_cnvex (syn_csset) p0025
  have p0027 := @g_wppimagefn (syn_ccnv (syn_csset)) p0026
  have p0028 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0029 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0028
  have p0030 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0027 p0029
  have p0031 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0024 p0030
  have p0032 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0033 := Nominal.mp p0031 p0032
  have p0034 := @g_inidm (syn_cvv)
  have p0035 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0034
  have p0036 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0033 p0035
  have p0037 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0003 p0036
  have p0038 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0002 p0037
  have p0039 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0040 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0039
  have p0041 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_cvv))
      p0038 p0040
  have p0042 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0012 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0034
  have p0047 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      p0044 p0046
  have p0048 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0003 p0047
  have p0049 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0050 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      p0049
  have p0051 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_cvv))
      p0048 p0050
  have p0052 := @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0002 p0051
  have p0053 := (Nominal.classEqRefl (syn_cwpphwgencnvfn))
  have p0054 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0053
  have p0055 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0052
      p0054
  have p0085 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0055 p0041
  have p0086 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0087 := Nominal.mp p0085 p0086
  have p0089 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0034
  have p0090 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0087 p0089
  have p0091 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
      p0003 p0090
  have p0092 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
      p0002 p0091
  have p0093 := (Nominal.classEqRefl (syn_cwpphwnisosetfn))
  have p0094 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwnisosetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))))
      p0093
  have p0095 :=
    @g_mpbir (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv))
      p0092 p0094
  have p0125 := @g_snex A
  have p0126 :=
    @g_fvtxpvv (syn_csn A) (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn) p0095 p0041 p0125
  have p0127 := @g_wpphwnisosetfnvalndv A hyp_wpphnpairfnvalndv_1
  have p0128 := @g_wpphwcnsetfnvalndv A hyp_wpphnpairfnvalndv_1
  have p0129 :=
    @g_opeq12i (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A)) (syn_chwniso A)
      (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A) p0127 p0128
  have p0130 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_csn A))
      (syn_cop (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A))
        (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)))
      (syn_cop (syn_chwniso A) (syn_chwcn A)) p0126 p0129
  have p0131 :=
    @g_eqtri (syn_cfv (syn_cwpphnpairfn) (syn_csn A))
      (syn_cfv (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_csn A))
      (syn_cop (syn_chwniso A) (syn_chwcn A)) p0001 p0130
  exact p0131


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part058`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wpphninputfnexndv :
    Nominal.NPrf (.classMem (syn_cwpphninputfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphninputfn))
  have p0001 := (Nominal.classEqRefl (syn_cwpphnpairfn))
  have p0002 := (Nominal.classEqRefl (syn_cwpphwnisosetfn))
  have p0003 := @g_swapex
  have p0004 := @g_imageex (syn_cswap) p0003
  have p0005 := @g_lnimageresfnex
  have p0006 := (Nominal.classEqRefl (syn_cwpphwgencnvfn))
  have p0009 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0011 := @g_vvex
  have p0012 := @g_snex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
  have p0013 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))
      p0011 p0012
  have p0014 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0019 := @g_snex (syn_ccnv (syn_chwcn (syn_cvv)))
  have p0020 := @g_xpex (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))) p0011 p0019
  have p0021 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0022 := @g_ssetex
  have p0023 := @g_cnvex (syn_csset) p0022
  have p0024 := @g_imageex (syn_ccnv (syn_csset)) p0023
  have p0025 :=
    @g_eqeltri (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv) p0021
      p0024
  have p0026 :=
    @g_txpex (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
      (syn_cwpppowsetfn) p0020 p0025
  have p0027 :=
    @g_coex (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0005 p0026
  have p0028 :=
    @g_coex (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0004 p0027
  have p0029 :=
    @g_eqeltri (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      (syn_cvv) p0014 p0028
  have p0030 :=
    @g_txpex
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn) p0013 p0029
  have p0031 :=
    @g_coex (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0005 p0030
  have p0032 :=
    @g_eqeltri (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      (syn_cvv) p0009 p0031
  have p0033 := @g_coex (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0004 p0032
  have p0034 :=
    @g_eqeltri (syn_cwpphwgencnvfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv) p0006 p0033
  have p0051 := @g_txpex (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn) p0034 p0029
  have p0052 :=
    @g_coex (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0005
      p0051
  have p0053 :=
    @g_coex (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
      p0004 p0052
  have p0054 :=
    @g_eqeltri (syn_cwpphwnisosetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))))
      (syn_cvv) p0002 p0053
  have p0071 := @g_txpex (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn) p0054 p0029
  have p0072 :=
    @g_eqeltri (syn_cwpphnpairfn) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn))
      (syn_cvv) p0001 p0071
  have p0073 := @g_siex (syn_cwpphnpairfn) p0072
  have p0074 :=
    @g_eqeltri (syn_cwpphninputfn) (syn_csi (syn_cwpphnpairfn)) (syn_cvv) p0000 p0073
  exact p0074

@[expose]
noncomputable def g_wpphninputfnmapndv :
    Nominal.NPrf (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) :=
  by
  have p0000 := @g_imageswapfn
  have p0001 := @g_lnimageresfnfn
  have p0004 := @g_hwgenex
  have p0005 := @g_hwbijex
  have p0006 := @g_vvex
  have p0007 := @g_xpex (syn_chwbij) (syn_cvv) p0005 p0006
  have p0008 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cvv)
  have p0010 := Nominal.mp p0008 p0009
  have p0013 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0014 := @g_hwcodesunivndv
  have p0015 := @g_weex
  have p0016 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0014 p0015
  have p0017 := @g_hwrelsex
  have p0018 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0016 p0017
  have p0019 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0013 p0018
  have p0020 := @g_cnvex (syn_chwcn (syn_cvv)) p0019
  have p0021 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @g_ssetex
  have p0024 := @g_cnvex (syn_csset) p0023
  have p0025 := @g_wppimagefn (syn_ccnv (syn_csset)) p0024
  have p0026 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0027 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0026
  have p0028 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0025 p0027
  have p0029 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0022 p0028
  have p0030 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := @g_inidm (syn_cvv)
  have p0033 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0032
  have p0034 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0031 p0033
  have p0035 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0001 p0034
  have p0036 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0000 p0035
  have p0037 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_cvv))
      p0036 p0038
  have p0040 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0010 p0039
  have p0041 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)
  have p0042 := Nominal.mp p0040 p0041
  have p0044 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0032
  have p0045 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      p0042 p0044
  have p0046 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0001 p0045
  have p0047 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      p0047
  have p0049 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_cvv))
      p0046 p0048
  have p0050 := @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0000 p0049
  have p0051 := (Nominal.classEqRefl (syn_cwpphwgencnvfn))
  have p0052 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0051
  have p0053 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0050
      p0052
  have p0083 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0053 p0039
  have p0084 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0085 := Nominal.mp p0083 p0084
  have p0087 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0032
  have p0088 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0085 p0087
  have p0089 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
      p0001 p0088
  have p0090 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
      p0000 p0089
  have p0091 := (Nominal.classEqRefl (syn_cwpphwnisosetfn))
  have p0092 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwnisosetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))))
      p0091
  have p0093 :=
    @g_mpbir (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv))
      p0090 p0092
  have p0123 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0093 p0039
  have p0124 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)
  have p0125 := Nominal.mp p0123 p0124
  have p0127 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0032
  have p0128 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0125 p0127
  have p0129 := (Nominal.classEqRefl (syn_cwpphnpairfn))
  have p0130 :=
    @g_fneq1i (syn_cvv) (syn_cwpphnpairfn)
      (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0129
  have p0131 :=
    @g_mpbir (syn_wfn (syn_cwpphnpairfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0128 p0130
  have p0132 := @g_ssv (syn_crn (syn_cwpphnpairfn))
  have p0133 :=
    @g_pm3_2i (syn_wfn (syn_cwpphnpairfn) (syn_cvv))
      (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv)) p0131 p0132
  have p0134 := (Nominal.biimpRefl (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv)))
  have p0135 :=
    @g_mpbir (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv))
      (syn_wa (syn_wfn (syn_cwpphnpairfn) (syn_cvv))
        (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv)))
      p0133 p0134
  have p0136 := @g_sifmap (syn_cvv) (syn_cvv) (syn_cwpphnpairfn)
  have p0137 := Nominal.mp p0135 p0136
  have p0138 := (Nominal.classEqRefl (syn_cwpphninputfn))
  have p0139 :=
    @g_feq1i (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
      (syn_csi (syn_cwpphnpairfn)) p0138
  have p0140 :=
    @g_mpbir (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))
      (syn_wf (syn_csi (syn_cwpphnpairfn)) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))
      p0137 p0139
  exact p0140

@[expose]
noncomputable def g_wpphninputfnvalndv (A : Class)
    (hyp_wpphninputfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A)))
        (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphninputfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn A)) (syn_cwpphninputfn) (syn_csi (syn_cwpphnpairfn)) p0000
  have p0002 := @g_snex A
  have p0003 := @g_imageswapfn
  have p0004 := @g_lnimageresfnfn
  have p0007 := @g_hwgenex
  have p0008 := @g_hwbijex
  have p0009 := @g_vvex
  have p0010 := @g_xpex (syn_chwbij) (syn_cvv) p0008 p0009
  have p0011 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0007 p0010
  have p0012 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0016 := (Nominal.classEqRefl (syn_chwcn (syn_cvv)))
  have p0017 := @g_hwcodesunivndv
  have p0018 := @g_weex
  have p0019 := @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0017 p0018
  have p0020 := @g_hwrelsex
  have p0021 := @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0019 p0020
  have p0022 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels))
      (syn_cvv) p0016 p0021
  have p0023 := @g_cnvex (syn_chwcn (syn_cvv)) p0022
  have p0024 := @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_ssetex
  have p0027 := @g_cnvex (syn_csset) p0026
  have p0028 := @g_wppimagefn (syn_ccnv (syn_csset)) p0027
  have p0029 := (Nominal.classEqRefl (syn_cwpppowsetfn))
  have p0030 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0029
  have p0031 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0028 p0030
  have p0032 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0025 p0031
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0034 := Nominal.mp p0032 p0033
  have p0035 := @g_inidm (syn_cvv)
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0035
  have p0037 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)) (syn_cvv))
      p0034 p0036
  have p0038 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
        (syn_cwpppowsetfn))
      p0004 p0037
  have p0039 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn)
        (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
          (syn_cwpppowsetfn)))
      p0003 p0038
  have p0040 := (Nominal.classEqRefl (syn_cwpphwcnsetfn))
  have p0041 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
            (syn_cwpppowsetfn))))
      p0040
  have p0042 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))))
              (syn_cwpppowsetfn)))) (syn_cvv))
      p0039 p0041
  have p0043 :=
    @g_pm3_2i
      (syn_wfn (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0013 p0042
  have p0044 :=
    @g_fntxp (syn_cvv) (syn_cvv)
      (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
      (syn_cwpphwcnsetfn)
  have p0045 := Nominal.mp p0043 p0044
  have p0047 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0035
  have p0048 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)) (syn_cvv))
      p0045 p0047
  have p0049 :=
    @g_fncovv (syn_clnimageresfn)
      (syn_ctxp (syn_cxp (syn_cvv)
          (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
        (syn_cwpphwcnsetfn))
      p0004 p0048
  have p0050 := (Nominal.classEqRefl (syn_cwpphwgendomfn))
  have p0051 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn)
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
            (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
          (syn_cwpphwcnsetfn)))
      p0050
  have p0052 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv)
              (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))))
            (syn_cwpphwcnsetfn))) (syn_cvv))
      p0049 p0051
  have p0053 := @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0003 p0052
  have p0054 := (Nominal.classEqRefl (syn_cwpphwgencnvfn))
  have p0055 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0054
  have p0056 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0053
      p0055
  have p0086 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0056 p0042
  have p0087 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0088 := Nominal.mp p0086 p0087
  have p0090 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0035
  have p0091 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0088 p0090
  have p0092 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
      p0004 p0091
  have p0093 :=
    @g_fncovv (syn_cimage (syn_cswap))
      (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
      p0003 p0092
  have p0094 := (Nominal.classEqRefl (syn_cwpphwnisosetfn))
  have p0095 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwnisosetfn)
      (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
          (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))))
      p0094
  have p0096 :=
    @g_mpbir (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn)
            (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv))
      p0093 p0095
  have p0126 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv))
      (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0096 p0042
  have p0127 := @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)
  have p0128 := Nominal.mp p0126 p0127
  have p0130 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv)
      (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0035
  have p0131 :=
    @g_mpbi
      (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn))
        (syn_cin (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0128 p0130
  have p0132 := (Nominal.classEqRefl (syn_cwpphnpairfn))
  have p0133 :=
    @g_fneq1i (syn_cvv) (syn_cwpphnpairfn)
      (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0132
  have p0134 :=
    @g_mpbir (syn_wfn (syn_cwpphnpairfn) (syn_cvv))
      (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0131 p0133
  have p0135 := @g_ssv (syn_crn (syn_cwpphnpairfn))
  have p0136 :=
    @g_pm3_2i (syn_wfn (syn_cwpphnpairfn) (syn_cvv))
      (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv)) p0134 p0135
  have p0137 := (Nominal.biimpRefl (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv)))
  have p0138 :=
    @g_mpbir (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv))
      (syn_wa (syn_wfn (syn_cwpphnpairfn) (syn_cvv))
        (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv)))
      p0136 p0137
  have p0139 := @g_sifvald (syn_cvv) (syn_cvv) (syn_csn A) (syn_cwpphnpairfn) p0138
  have p0140 := Nominal.mp p0002 p0139
  have p0141 := @g_wpphnpairfnvalndv A hyp_wpphninputfnvalndv_1
  have p0142 :=
    @g_sneqi (syn_cfv (syn_cwpphnpairfn) (syn_csn A))
      (syn_cop (syn_chwniso A) (syn_chwcn A)) p0141
  have p0143 :=
    @g_eqtri (syn_cfv (syn_csi (syn_cwpphnpairfn)) (syn_csn (syn_csn A)))
      (syn_csn (syn_cfv (syn_cwpphnpairfn) (syn_csn A)))
      (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))) p0140 p0142
  have p0144 :=
    @g_eqtri (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A)))
      (syn_cfv (syn_csi (syn_cwpphnpairfn)) (syn_csn (syn_csn A)))
      (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))) p0001 p0143
  exact p0144

@[expose]
noncomputable def g_fdpointimagevvdndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv))
        (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A)))
          (syn_cpw1 (syn_cpw1 A)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
  have dv_cache_0001 : c ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : c ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0003 :
    c ∉
      ((Wff.imp (.classMem A (syn_cvv))
          (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A)))
            (syn_cpw1 (syn_cpw1 A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_c_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (.classMem A (syn_cvv))
  have p0001 := @g_id (.classEq (.cv c) A)
  have p0002 := @g_eleq1d (.classEq (.cv c) A) (.cv c) A (syn_cvv) p0001
  have p0004 := @g_sneqd (.classEq (.cv c) A) (.cv c) A p0001
  have p0005 := @g_sneqd (.classEq (.cv c) A) (syn_csn (.cv c)) (syn_csn A) p0004
  have p0006 :=
    @g_imaeq2d (.classEq (.cv c) A) (syn_csn (syn_csn (.cv c))) (syn_csn (syn_csn A))
      (syn_cfdpointrel (syn_cvv)) p0005
  have p0008 := @g_pw1eq (.cv c) A
  have p0009 :=
    @g_syl (.classEq (.cv c) A) (.classEq (.cv c) A)
      (.classEq (syn_cpw1 (.cv c)) (syn_cpw1 A)) p0001 p0008
  have p0010 := @g_pw1eq (syn_cpw1 (.cv c)) (syn_cpw1 A)
  have p0011 :=
    @g_syl (.classEq (.cv c) A) (.classEq (syn_cpw1 (.cv c)) (syn_cpw1 A))
      (.classEq (syn_cpw1 (syn_cpw1 (.cv c))) (syn_cpw1 (syn_cpw1 A))) p0009 p0010
  have p0012 :=
    @g_eqeq12d (.classEq (.cv c) A)
      (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn (.cv c))))
      (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A)))
      (syn_cpw1 (syn_cpw1 (.cv c))) (syn_cpw1 (syn_cpw1 A)) p0006 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv c) A) (.classMem (.cv c) (syn_cvv)) (.classMem A (syn_cvv))
      (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn (.cv c))))
        (syn_cpw1 (syn_cpw1 (.cv c))))
      (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A)))
        (syn_cpw1 (syn_cpw1 A)))
      p0002 p0012
  have p0014 := @g_vvex
  have p0015 := @g_fdpointimage (syn_cvv) c dv_cache_0001 p0014
  have p0016 :=
    @g_vtoclg
      (.imp (.classMem (.cv c) (syn_cvv))
        (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn (.cv c))))
          (syn_cpw1 (syn_cpw1 (.cv c)))))
      (.imp (.classMem A (syn_cvv))
        (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A)))
          (syn_cpw1 (syn_cpw1 A))))
      c A (syn_cvv) dv_cache_0002 dv_cache_0003 p0013 p0015
  have p0017 :=
    @g_mpd (.classMem A (syn_cvv)) (.classMem A (syn_cvv))
      (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A)))
        (syn_cpw1 (syn_cpw1 A)))
      p0000 p0016
  exact p0017

@[expose]
noncomputable def g_wppqkrelkernelexndv :
    Nominal.NPrf (.classMem (syn_cwppqkrelkernel) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppqkrelkernel))
  have p0001 := @g_vvex
  have p0004 := @g_xpkex (syn_cvv) (syn_cvv) p0001 p0001
  have p0005 := @g_xpkex (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)) p0001 p0004
  have p0006 := @g_setconslem5
  have p0007 :=
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
      p0005 p0006
  have p0008 :=
    @g_eqeltri (syn_cwppqkrelkernel)
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
      (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_wppqkrelkernelvalndv (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cimak (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A))) (syn_cqkrel A)) :=
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
  have p0000 := (Nominal.classEqRefl (syn_cwppqkrelkernel))
  have p0001 :=
    @g_imakeq1i (syn_cwppqkrelkernel)
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
      (syn_cpw1 (syn_cpw1 A)) p0000
  have p0002 :=
    @g_setconslem6 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_eqtr4i
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
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.classMem (syn_cop (.cv x) (.cv y)) A)))))
      (syn_cqkrel A) p0002 p0003
  have p0005 :=
    @g_eqtri (syn_cimak (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A)))
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
      (syn_cqkrel A) p0001 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part059`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisolnkereqndv (A : Class)
    (hyp_hwnisolnkereqndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_clnker (syn_chwniso A)) (syn_chwniso A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_clnker (syn_chwniso A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_clnker (syn_chwniso A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_brlnker (syn_chwniso A) (.cv x) (.cv y)
  have p0001 :=
    @g_simpl (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
      (syn_wbr (.cv y) (syn_chwniso A) (.cv x))
  have p0002 := @g_id (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
  have p0003 := @g_hwnisoerv A
  have p0004 := Nominal.mp hyp_hwnisolnkereqndv_1 p0003
  have p0005 :=
    @g_a1i (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv))
      (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) p0004
  have p0006 := @g_brreldmex (.cv x) (.cv y) (syn_chwniso A)
  have p0007 := @g_brrelrnex (.cv x) (.cv y) (syn_chwniso A)
  have p0009 :=
    @g_ersym (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_cvv) (syn_chwniso A) (.cv x)
      (.cv y) p0005 p0006 p0007 p0002
  have p0010 :=
    @g_jca (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
      (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) (syn_wbr (.cv y) (syn_chwniso A) (.cv x))
      p0002 p0009
  have p0011 :=
    @g_impbii
      (syn_wa (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
        (syn_wbr (.cv y) (syn_chwniso A) (.cv x)))
      (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) p0001 p0010
  have p0012 :=
    @g_bitri (syn_wbr (.cv x) (syn_clnker (syn_chwniso A)) (.cv y))
      (syn_wa (syn_wbr (.cv x) (syn_chwniso A) (.cv y))
        (syn_wbr (.cv y) (syn_chwniso A) (.cv x)))
      (syn_wbr (.cv x) (syn_chwniso A) (.cv y)) p0000 p0011
  have p0013 :=
    @g_eqbrriv x y (syn_clnker (syn_chwniso A)) (syn_chwniso A) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0012
  exact p0013

@[expose]
noncomputable def g_lnpwhnordvalndv (A : Class)
    (hyp_lnpwhnordvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))))
        (syn_chnord A)) :=
  by
  have p0000 := @g_hwnisoex A hyp_lnpwhnordvalndv_1
  have p0001 := @g_hwcnex A hyp_lnpwhnordvalndv_1
  have p0002 := @g_lnpwquofnval (syn_chwcn A) (syn_chwniso A) p0000 p0001
  have p0003 := @g_hwnisolnkereqndv A hyp_lnpwhnordvalndv_1
  have p0004 := @g_qseq2 (syn_clnker (syn_chwniso A)) (syn_chwniso A) (syn_chwcn A)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := (Nominal.classEqRefl (syn_chnord A))
  have p0007 := @g_eqcomi (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) p0006
  have p0008 :=
    @g_eqtri (syn_cqs (syn_chwcn A) (syn_clnker (syn_chwniso A)))
      (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_chnord A) p0005 p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))))
      (syn_cqs (syn_chwcn A) (syn_clnker (syn_chwniso A))) (syn_chnord A) p0002 p0008
  exact p0009

@[expose]
noncomputable def g_wpplitphnordpointfnexndv :
    Nominal.NPrf (.classMem (syn_cwpplitphnordpointfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpplitphnordpointfn))
  have p0001 := @g_lnpwquofnex
  have p0002 := @g_wpphninputfnexndv
  have p0003 := @g_coex (syn_clnpwquofn) (syn_cwpphninputfn) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cwpplitphnordpointfn) (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn))
      (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_wpplitphnordpointfnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cvv))) :=
  by
  have p0000 := @g_lnpwquofnfn
  have p0001 := @g_wpphninputfnmapndv
  have p0002 := @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_dffn2 (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
  have p0005 :=
    @g_mpbi (syn_wfn (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)))
      (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_clnpwquofn) (syn_cvv))
      (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cvv)) p0000 p0005
  have p0007 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cvv)) (syn_clnpwquofn) (syn_cwpphninputfn)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (syn_cwpplitphnordpointfn))
  have p0010 :=
    @g_fneq1i (syn_cpw1 (syn_cvv)) (syn_cwpplitphnordpointfn)
      (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) p0009
  have p0011 :=
    @g_mpbir (syn_wfn (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cvv)))
      (syn_wfn (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_cpw1 (syn_cvv))) p0008
      p0010
  exact p0011

@[expose]
noncomputable def g_wpplitphnordpointfnvalndv (A : Class)
    (hyp_wpplitphnordpointfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn A))) (syn_chnord A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpplitphnordpointfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn A)) (syn_cwpplitphnordpointfn)
      (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) p0000
  have p0002 := @g_wpphninputfnmapndv
  have p0003 := @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_snex A
  have p0006 := @g_snelpw1 (syn_csn A) (syn_cvv)
  have p0007 :=
    @g_mpbir (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn A) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv))) p0004 p0007
  have p0009 :=
    @g_fvco2 (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn A)) (syn_clnpwquofn)
      (syn_cwpphninputfn)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_wpphninputfnvalndv A hyp_wpplitphnordpointfnvalndv_1
  have p0012 :=
    @g_fveq2i (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A)))
      (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))) (syn_clnpwquofn) p0011
  have p0013 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_csn (syn_csn A)))
      (syn_cfv (syn_clnpwquofn) (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A))))
      (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) p0010
      p0012
  have p0014 := @g_lnpwhnordvalndv A hyp_wpplitphnordpointfnvalndv_1
  have p0015 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_csn (syn_csn A)))
      (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))))
      (syn_chnord A) p0013 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn A)))
      (syn_cfv (syn_ccom (syn_clnpwquofn) (syn_cwpphninputfn)) (syn_csn (syn_csn A)))
      (syn_chnord A) p0001 p0015
  exact p0016

@[expose]
noncomputable def g_hncardnceqsetimpndv (D : Class) (E : Class) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cvv)) (.imp (.classEq (syn_cnc D) (syn_cnc E))
          (.classEq (syn_chncard D) (syn_chncard E)))) :=
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
  have p0000 := @g_eqncg D E (syn_cvv)
  have p0001 :=
    @g_biimpd (.classMem D (syn_cvv)) (.classEq (syn_cnc D) (syn_cnc E))
      (syn_wbr D (syn_cen) E) p0000
  have p0002 := @g_bren D E f dv_cache_0001 dv_cache_0002
  have p0003 := @g_biimpi (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0002
  have p0004 :=
    @g_syl6 (.classMem D (syn_cvv)) (.classEq (syn_cnc D) (syn_cnc E))
      (syn_wbr D (syn_cen) E) (syn_wex f (syn_wf1o (.cv f) D E)) p0001 p0003
  have p0005 := @g_vex f
  have p0006 := @g_hncardf1oimpndv D E (.cv f) p0005
  have p0007 :=
    @g_exlimiv (syn_wf1o (.cv f) D E) (.classEq (syn_chncard D) (syn_chncard E)) f
      dv_cache_0003 p0006
  have p0008 :=
    @g_syl6 (.classMem D (syn_cvv)) (.classEq (syn_cnc D) (syn_cnc E))
      (syn_wex f (syn_wf1o (.cv f) D E)) (.classEq (syn_chncard D) (syn_chncard E)) p0004
      p0007
  exact p0008

@[expose]
noncomputable def g_hnordncmemimpndv (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnc A)) (.classMem (syn_chnord B) (syn_cnc (syn_chnord A)))) :=
  by
  have p0000 := @g_elex B (syn_cnc A)
  have p0001 := @g_hnordexg B
  have p0002 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem B (syn_cvv))
      (.classMem (syn_chnord B) (syn_cvv)) p0000 p0001
  have p0003 := @g_ncidg (syn_chnord B) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem (syn_chnord B) (syn_cvv))
      (.classMem (syn_chnord B) (syn_cnc (syn_chnord B))) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_chncard B))
  have p0006 := @g_eqcomi (syn_chncard B) (syn_cnc (syn_chnord B)) p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cnc (syn_chnord B)) (syn_chncard B)) (.classMem B (syn_cnc A))
      p0006
  have p0008 := @g_elnc B A
  have p0009 := @g_biimpi (.classMem B (syn_cnc A)) (syn_wbr B (syn_cen) A) p0008
  have p0011 := @g_eqncg B A (syn_cvv)
  have p0012 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem B (syn_cvv))
      (syn_wb (.classEq (syn_cnc B) (syn_cnc A)) (syn_wbr B (syn_cen) A)) p0000 p0011
  have p0013 :=
    @g_mpbird (.classMem B (syn_cnc A)) (.classEq (syn_cnc B) (syn_cnc A))
      (syn_wbr B (syn_cen) A) p0009 p0012
  have p0015 := @g_hncardnceqsetimpndv B A
  have p0016 :=
    @g_syl (.classMem B (syn_cnc A)) (.classMem B (syn_cvv))
      (.imp (.classEq (syn_cnc B) (syn_cnc A)) (.classEq (syn_chncard B) (syn_chncard A)))
      p0000 p0015
  have p0017 :=
    @g_mpd (.classMem B (syn_cnc A)) (.classEq (syn_cnc B) (syn_cnc A))
      (.classEq (syn_chncard B) (syn_chncard A)) p0013 p0016
  have p0018 :=
    @g_eqtrd (.classMem B (syn_cnc A)) (syn_cnc (syn_chnord B)) (syn_chncard B)
      (syn_chncard A) p0007 p0017
  have p0019 := (Nominal.classEqRefl (syn_chncard A))
  have p0020 :=
    @g_a1i (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) (.classMem B (syn_cnc A))
      p0019
  have p0021 :=
    @g_eqtrd (.classMem B (syn_cnc A)) (syn_cnc (syn_chnord B)) (syn_chncard A)
      (syn_cnc (syn_chnord A)) p0018 p0020
  have p0022 :=
    @g_eleqtrd (.classMem B (syn_cnc A)) (syn_chnord B) (syn_cnc (syn_chnord B))
      (syn_cnc (syn_chnord A)) p0004 p0021
  exact p0022

@[expose]
noncomputable def g_enimasatndv (A : Class) (Q : Class)
    (hyp_enimasatndv_1 : Nominal.NPrf (.classMem A Q))
    (hyp_enimasatndv_2 : Nominal.NPrf (syn_wss Q (syn_cnc A))) :
    Nominal.NPrf (.classEq (syn_cima (syn_cen) Q) (syn_cnc A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Q : y ∉ Q.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cen)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ (Q).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_Q, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) (syn_cnc A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cima (syn_cen) Q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_x_not_Q, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_A,
          not_false_eq_true])
  have p0000 := @g_elima y (.cv x) (syn_cen) Q dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_biimpi (.classMem (.cv x) (syn_cima (syn_cen) Q))
      (syn_wrex y Q (syn_wbr (.cv y) (syn_cen) (.cv x))) p0000
  have p0002 := @g_simpr (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))
  have p0003 := @g_ensymi (.cv y) (.cv x)
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x)))
      (syn_wbr (.cv y) (syn_cen) (.cv x)) (syn_wbr (.cv x) (syn_cen) (.cv y)) p0002 p0003
  have p0005 := @g_simpl (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x))
  have p0006 := @g_sseli Q (syn_cnc A) (.cv y) hyp_enimasatndv_2
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x)))
      (.classMem (.cv y) Q) (.classMem (.cv y) (syn_cnc A)) p0005 p0006
  have p0008 := @g_elnc (.cv y) A
  have p0009 :=
    @g_sylib (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x)))
      (.classMem (.cv y) (syn_cnc A)) (syn_wbr (.cv y) (syn_cen) A) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x)))
      (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (.cv y) (syn_cen) A) p0004 p0009
  have p0011 := @g_entr (.cv x) (.cv y) A
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x)))
      (syn_wa (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (.cv y) (syn_cen) A))
      (syn_wbr (.cv x) (syn_cen) A) p0010 p0011
  have p0013 := @g_elnc (.cv x) A
  have p0014 :=
    @g_sylibr (syn_wa (.classMem (.cv y) Q) (syn_wbr (.cv y) (syn_cen) (.cv x)))
      (syn_wbr (.cv x) (syn_cen) A) (.classMem (.cv x) (syn_cnc A)) p0012 p0013
  have p0015 :=
    @g_rexlimiva (syn_wbr (.cv y) (syn_cen) (.cv x)) (.classMem (.cv x) (syn_cnc A)) y Q
      dv_cache_0004 p0014
  have p0016 :=
    @g_syl (.classMem (.cv x) (syn_cima (syn_cen) Q))
      (syn_wrex y Q (syn_wbr (.cv y) (syn_cen) (.cv x))) (.classMem (.cv x) (syn_cnc A))
      p0001 p0015
  have p0017 :=
    @g_ssriv x (syn_cima (syn_cen) Q) (syn_cnc A) dv_cache_0005 dv_cache_0006 p0016
  have p0018 := (Nominal.classEqRefl (syn_cnc A))
  have p0019 := (Nominal.classEqRefl (syn_cec A (syn_cen)))
  have p0020 :=
    @g_eqtri (syn_cnc A) (syn_cec A (syn_cen)) (syn_cima (syn_cen) (syn_csn A)) p0018
      p0019
  have p0021 := @g_snssi A Q
  have p0022 := Nominal.mp hyp_enimasatndv_1 p0021
  have p0023 := @g_imass2 (syn_csn A) Q (syn_cen)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_eqsstri (syn_cnc A) (syn_cima (syn_cen) (syn_csn A)) (syn_cima (syn_cen) Q) p0020
      p0024
  have p0026 := @g_eqssi (syn_cima (syn_cen) Q) (syn_cnc A) p0017 p0025
  exact p0026

@[expose]
noncomputable def g_wpplitphnordpointfnvalimpndv (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv q))
          (syn_chnord (syn_cuni (syn_cuni (.cv q)))))) :=
  by
  have dv_cache_0001 : q ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_fdcolcodearg (syn_cvv) q dv_cache_0001
  have p0001 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0002 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv))
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000 p0001
  have p0003 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.cv q)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cwpplitphnordpointfn) p0002
  have p0004 := @g_vex q
  have p0005 := @g_uniex (.cv q) p0004
  have p0006 := @g_uniex (syn_cuni (.cv q)) p0005
  have p0007 := @g_wpplitphnordpointfnvalndv (syn_cuni (syn_cuni (.cv q))) p0006
  have p0008 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwpplitphnordpointfn)
          (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
        (syn_chnord (syn_cuni (syn_cuni (.cv q)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0007
  have p0009 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_cfv (syn_cwpplitphnordpointfn) (.cv q))
      (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_chnord (syn_cuni (syn_cuni (.cv q)))) p0003 p0008
  exact p0009

@[expose]
noncomputable def g_wpplitphnordimexndv (Q : Class)
    (hyp_wpplitphnordimexndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) (syn_cvv)) :=
  by
  have p0000 := @g_wpplitphnordpointfnexndv
  have p0001 := @g_pw1ex Q hyp_wpplitphnordimexndv_1
  have p0002 := @g_pw1ex (syn_cpw1 Q) p0001
  have p0003 := @g_imaex (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_wpplitphnordimcanndv (C : Class) (Q : Class)
    (_hyp_wpplitphnordimcanndv_1 : Nominal.NPrf (.classMem Q (syn_cvv)))
    (hyp_wpplitphnordimcanndv_2 : Nominal.NPrf (.classMem C Q)) :
    Nominal.NPrf
      (.classMem (syn_chnord C)
        (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) :=
  by
  have p0000 := @g_elexi C Q hyp_wpplitphnordimcanndv_2
  have p0001 := @g_wpplitphnordpointfnvalndv C p0000
  have p0002 :=
    @g_eqcomi (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn C))) (syn_chnord C)
      p0001
  have p0003 := @g_snelpw1 C Q
  have p0004 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 Q)) (.classMem C Q)
      hyp_wpplitphnordimcanndv_2 p0003
  have p0005 := @g_snelpw1 (syn_csn C) (syn_cpw1 Q)
  have p0006 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cpw1 Q)))
      (.classMem (syn_csn C) (syn_cpw1 Q)) p0004 p0005
  have p0007 := @g_wpplitphnordpointfnfnndv
  have p0008 := @g_fnfun (syn_cpw1 (syn_cvv)) (syn_cwpplitphnordpointfn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_snex C
  have p0011 := @g_snelpw1 (syn_csn C) (syn_cvv)
  have p0012 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn C) (syn_cvv)) p0010 p0011
  have p0014 := @g_fndm (syn_cpw1 (syn_cvv)) (syn_cwpplitphnordpointfn)
  have p0015 := Nominal.mp p0007 p0014
  have p0016 :=
    @g_eleq2i (syn_cdm (syn_cwpplitphnordpointfn)) (syn_cpw1 (syn_cvv))
      (syn_csn (syn_csn C)) p0015
  have p0017 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpplitphnordpointfn)))
      (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv))) p0012 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfun (syn_cwpplitphnordpointfn))
      (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpplitphnordpointfn))) p0009 p0017
  have p0019 :=
    @g_funfvima (syn_cpw1 (syn_cpw1 Q)) (syn_csn (syn_csn C)) (syn_cwpplitphnordpointfn)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := Nominal.mp p0006 p0020
  have p0022 :=
    @g_eqeltri (syn_chnord C) (syn_cfv (syn_cwpplitphnordpointfn) (syn_csn (syn_csn C)))
      (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) p0002 p0021
  exact p0022

@[expose]
noncomputable def g_wpplitphnordimssndv (C : Class) (Q : Class)
    (_hyp_wpplitphnordimssndv_1 : Nominal.NPrf (.classMem Q (syn_cvv)))
    (hyp_wpplitphnordimssndv_2 : Nominal.NPrf (syn_wss Q (syn_cnc C))) :
    Nominal.NPrf
      (syn_wss (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))
        (syn_cnc (syn_chnord C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Q : y ∉ Q.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_cpw1 (syn_cpw1 Q))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_Q,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cwpplitphnordpointfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ (Q).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_Q, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (syn_cnc (syn_chnord C)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpplitphnordpointfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_y_not_Q, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cnc (syn_chnord C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, fresh_y_not_C,
          not_false_eq_true])
  have p0000 := @g_wpplitphnordpointfnfnndv
  have p0001 := @g_ssv (syn_cpw1 Q)
  have p0002 := @g_pw1ss (syn_cpw1 Q) (syn_cvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cvv)))
      (syn_wss (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cvv))) p0000 p0003
  have p0005 :=
    @g_fvelimab x (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cpw1 Q)) (.cv y)
      (syn_cwpplitphnordpointfn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_biimpi
      (.classMem (.cv y) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_wrex x (syn_cpw1 (syn_cpw1 Q))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      p0006
  have p0008 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0009 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0010 := @g_ssv Q
  have p0011 := @g_pw1ss Q (syn_cvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_pw1ss (syn_cpw1 Q) (syn_cpw1 (syn_cvv))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseli (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cpw1 (syn_cvv))) (.cv x) p0014
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0009 p0015
  have p0017 := @g_wpplitphnordpointfnvalimpndv x
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x))
        (syn_chnord (syn_cuni (syn_cuni (.cv x)))))
      p0016 p0017
  have p0020 := @g_fdcolcodearg Q x dv_cache_0004
  have p0021 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
        (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x)))))))
      p0009 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
      (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
        (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x)))))))
      (.classMem (syn_cuni (syn_cuni (.cv x))) Q) p0021 p0022
  have p0024 :=
    @g_sseli Q (syn_cnc C) (syn_cuni (syn_cuni (.cv x))) hyp_wpplitphnordimssndv_2
  have p0025 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
      (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C)) p0023 p0024
  have p0026 := @g_hnordncmemimpndv C (syn_cuni (syn_cuni (.cv x)))
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C))
      (.classMem (syn_chnord (syn_cuni (syn_cuni (.cv x)))) (syn_cnc (syn_chnord C)))
      p0025 p0026
  have p0028 :=
    @g_eqeltrd
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (syn_cfv (syn_cwpplitphnordpointfn) (.cv x))
      (syn_chnord (syn_cuni (syn_cuni (.cv x)))) (syn_cnc (syn_chnord C)) p0018 p0027
  have p0029 :=
    @g_eqeltrrd
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y) (syn_cnc (syn_chnord C)) p0008
      p0028
  have p0030 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y))
      (.classMem (.cv y) (syn_cnc (syn_chnord C))) x (syn_cpw1 (syn_cpw1 Q)) dv_cache_0005
      p0029
  have p0031 :=
    @g_syl
      (.classMem (.cv y) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_wrex x (syn_cpw1 (syn_cpw1 Q))
        (.classEq (syn_cfv (syn_cwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv y) (syn_cnc (syn_chnord C))) p0007 p0030
  have p0032 :=
    @g_ssriv y (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))
      (syn_cnc (syn_chnord C)) dv_cache_0006 dv_cache_0007 p0031
  exact p0032

@[expose]
noncomputable def g_wpplitphnordcardvalndv (C : Class) (Q : Class)
    (hyp_wpplitphnordcardvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv)))
    (hyp_wpplitphnordcardvalndv_2 : Nominal.NPrf (.classMem C Q))
    (hyp_wpplitphnordcardvalndv_3 : Nominal.NPrf (syn_wss Q (syn_cnc C))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cimage (syn_cen))
          (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q)))) (syn_chncard C)) :=
  by
  have p0000 := @g_enex
  have p0001 := @g_wpplitphnordimexndv Q hyp_wpplitphnordcardvalndv_1
  have p0002 :=
    @g_fvimagecl (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) (syn_cen)
      p0000 p0001
  have p0003 :=
    @g_wpplitphnordimcanndv C Q hyp_wpplitphnordcardvalndv_1 hyp_wpplitphnordcardvalndv_2
  have p0004 :=
    @g_wpplitphnordimssndv C Q hyp_wpplitphnordcardvalndv_1 hyp_wpplitphnordcardvalndv_3
  have p0005 :=
    @g_enimasatndv (syn_chnord C)
      (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))) p0003 p0004
  have p0006 :=
    @g_eqtri
      (syn_cfv (syn_cimage (syn_cen))
        (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_cima (syn_cen) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_cnc (syn_chnord C)) p0002 p0005
  have p0007 := (Nominal.classEqRefl (syn_chncard C))
  have p0008 := @g_eqcomi (syn_chncard C) (syn_cnc (syn_chnord C)) p0007
  have p0009 :=
    @g_eqtri
      (syn_cfv (syn_cimage (syn_cen))
        (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_cnc (syn_chnord C)) (syn_chncard C) p0006 p0008
  exact p0009

@[expose]
noncomputable def g_wpppowset2fnexndv :
    Nominal.NPrf (.classMem (syn_cwpppowset2fn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowset2fn))
  have p0001 := @g_wpppowsetfnexndv
  have p0003 := @g_siex (syn_cwpppowsetfn) p0001
  have p0004 := @g_coex (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cwpppowset2fn)
      (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_cvv) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wpppowset2fnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwpppowset2fn) (syn_cpw1 (syn_cvv))) :=
  by
  have p0000 := @g_wpppowsetfnfnndv
  have p0002 := @g_ssv (syn_crn (syn_cwpppowsetfn))
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv)))
  have p0005 :=
    @g_mpbir (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv))
      (syn_wa (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
        (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)))
      p0003 p0004
  have p0006 := @g_sifmap (syn_cvv) (syn_cvv) (syn_cwpppowsetfn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwpppowsetfn))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_ssv (syn_crn (syn_csi (syn_cwpppowsetfn)))
  have p0011 :=
    @g_n_3pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wfn (syn_csi (syn_cwpppowsetfn)) (syn_cpw1 (syn_cvv)))
      (syn_wss (syn_crn (syn_csi (syn_cwpppowsetfn))) (syn_cvv)) p0000 p0009 p0010
  have p0012 :=
    @g_fnco (syn_cvv) (syn_cpw1 (syn_cvv)) (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := (Nominal.classEqRefl (syn_cwpppowset2fn))
  have p0015 :=
    @g_fneq1i (syn_cpw1 (syn_cvv)) (syn_cwpppowset2fn)
      (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) p0014
  have p0016 :=
    @g_mpbir (syn_wfn (syn_cwpppowset2fn) (syn_cpw1 (syn_cvv)))
      (syn_wfn (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_cpw1 (syn_cvv)))
      p0013 p0015
  exact p0016

@[expose]
noncomputable def g_wpppowset2fnvalndv (A : Class)
    (hyp_wpppowset2fnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn A))) (syn_cpw (syn_cpw A))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpppowset2fn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn A)) (syn_cwpppowset2fn)
      (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) p0000
  have p0002 := @g_wpppowsetfnfnndv
  have p0003 := @g_ssv (syn_crn (syn_cwpppowsetfn))
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
      (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)) p0002 p0003
  have p0005 := (Nominal.biimpRefl (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv)))
  have p0006 :=
    @g_mpbir (syn_wf (syn_cwpppowsetfn) (syn_cvv) (syn_cvv))
      (syn_wa (syn_wfn (syn_cwpppowsetfn) (syn_cvv))
        (syn_wss (syn_crn (syn_cwpppowsetfn)) (syn_cvv)))
      p0004 p0005
  have p0007 := @g_sifmap (syn_cvv) (syn_cvv) (syn_cwpppowsetfn)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwpppowsetfn))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_snex A
  have p0012 := @g_snelpw1 (syn_csn A) (syn_cvv)
  have p0013 :=
    @g_mpbir (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn A) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_cwpppowsetfn)) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn (syn_csn A)) (syn_cpw1 (syn_cvv))) p0010 p0013
  have p0015 :=
    @g_fvco2 (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn A)) (syn_cwpppowsetfn)
      (syn_csi (syn_cwpppowsetfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0023 := @g_sifvald (syn_cvv) (syn_cvv) (syn_csn A) (syn_cwpppowsetfn) p0006
  have p0024 := Nominal.mp p0011 p0023
  have p0025 := @g_wpppowsetfnvalndv A hyp_wpppowset2fnvalndv_1
  have p0026 := @g_sneqi (syn_cfv (syn_cwpppowsetfn) (syn_csn A)) (syn_cpw A) p0025
  have p0027 :=
    @g_eqtri (syn_cfv (syn_csi (syn_cwpppowsetfn)) (syn_csn (syn_csn A)))
      (syn_csn (syn_cfv (syn_cwpppowsetfn) (syn_csn A))) (syn_csn (syn_cpw A)) p0024 p0026
  have p0028 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_cwpppowsetfn)) (syn_csn (syn_csn A)))
      (syn_csn (syn_cpw A)) (syn_cwpppowsetfn) p0027
  have p0029 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_csn (syn_csn A)))
      (syn_cfv (syn_cwpppowsetfn) (syn_cfv (syn_csi (syn_cwpppowsetfn)) (syn_csn (syn_csn A))))
      (syn_cfv (syn_cwpppowsetfn) (syn_csn (syn_cpw A))) p0016 p0028
  have p0030 := @g_pwex A hyp_wpppowset2fnvalndv_1
  have p0031 := @g_wpppowsetfnvalndv (syn_cpw A) p0030
  have p0032 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_csn (syn_csn A)))
      (syn_cfv (syn_cwpppowsetfn) (syn_csn (syn_cpw A))) (syn_cpw (syn_cpw A)) p0029 p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn A)))
      (syn_cfv (syn_ccom (syn_cwpppowsetfn) (syn_csi (syn_cwpppowsetfn))) (syn_csn (syn_csn A)))
      (syn_cpw (syn_cpw A)) p0001 p0032
  exact p0033

@[expose]
noncomputable def g_wpppowset2fnvalimpndv (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv))))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv q))
          (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv q))))))) :=
  by
  have dv_cache_0001 : q ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_fdcolcodearg (syn_cvv) q dv_cache_0001
  have p0001 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
  have p0002 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) (syn_cvv))
        (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0000 p0001
  have p0003 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (.cv q)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_cwpppowset2fn) p0002
  have p0004 := @g_vex q
  have p0005 := @g_uniex (.cv q) p0004
  have p0006 := @g_uniex (syn_cuni (.cv q)) p0005
  have p0007 := @g_wpppowset2fnvalndv (syn_cuni (syn_cuni (.cv q))) p0006
  have p0008 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
        (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv q))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0007
  have p0009 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_cfv (syn_cwpppowset2fn) (.cv q))
      (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv q))))) p0003 p0008
  exact p0009

@[expose]
noncomputable def g_wpppowset2imexndv (Q : Class)
    (hyp_wpppowset2imexndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) (syn_cvv)) :=
  by
  have p0000 := @g_wpppowset2fnexndv
  have p0001 := @g_pw1ex Q hyp_wpppowset2imexndv_1
  have p0002 := @g_pw1ex (syn_cpw1 Q) p0001
  have p0003 := @g_imaex (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_wpppowset2imcanndv (C : Class) (Q : Class)
    (_hyp_wpppowset2imcanndv_1 : Nominal.NPrf (.classMem Q (syn_cvv)))
    (hyp_wpppowset2imcanndv_2 : Nominal.NPrf (.classMem C Q)) :
    Nominal.NPrf
      (.classMem (syn_cpw (syn_cpw C))
        (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))) :=
  by
  have p0000 := @g_elexi C Q hyp_wpppowset2imcanndv_2
  have p0001 := @g_wpppowset2fnvalndv C p0000
  have p0002 :=
    @g_eqcomi (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn C))) (syn_cpw (syn_cpw C))
      p0001
  have p0003 := @g_snelpw1 C Q
  have p0004 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 Q)) (.classMem C Q) hyp_wpppowset2imcanndv_2
      p0003
  have p0005 := @g_snelpw1 (syn_csn C) (syn_cpw1 Q)
  have p0006 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cpw1 Q)))
      (.classMem (syn_csn C) (syn_cpw1 Q)) p0004 p0005
  have p0007 := @g_wpppowset2fnfnndv
  have p0008 := @g_fnfun (syn_cpw1 (syn_cvv)) (syn_cwpppowset2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_snex C
  have p0011 := @g_snelpw1 (syn_csn C) (syn_cvv)
  have p0012 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn C) (syn_cvv)) p0010 p0011
  have p0014 := @g_fndm (syn_cpw1 (syn_cvv)) (syn_cwpppowset2fn)
  have p0015 := Nominal.mp p0007 p0014
  have p0016 :=
    @g_eleq2i (syn_cdm (syn_cwpppowset2fn)) (syn_cpw1 (syn_cvv)) (syn_csn (syn_csn C))
      p0015
  have p0017 :=
    @g_mpbir (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpppowset2fn)))
      (.classMem (syn_csn (syn_csn C)) (syn_cpw1 (syn_cvv))) p0012 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfun (syn_cwpppowset2fn))
      (.classMem (syn_csn (syn_csn C)) (syn_cdm (syn_cwpppowset2fn))) p0009 p0017
  have p0019 :=
    @g_funfvima (syn_cpw1 (syn_cpw1 Q)) (syn_csn (syn_csn C)) (syn_cwpppowset2fn)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := Nominal.mp p0006 p0020
  have p0022 :=
    @g_eqeltri (syn_cpw (syn_cpw C)) (syn_cfv (syn_cwpppowset2fn) (syn_csn (syn_csn C)))
      (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) p0002 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part060`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wpppowset2imssndv (C : Class) (Q : Class)
    (_hyp_wpppowset2imssndv_1 : Nominal.NPrf (.classMem Q (syn_cvv)))
    (hyp_wpppowset2imssndv_2 : Nominal.NPrf (syn_wss Q (syn_cnc C))) :
    Nominal.NPrf
      (syn_wss (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))
        (syn_cnc (syn_cpw (syn_cpw C)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ Q.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Q : y ∉ Q.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Q : x ∉ Q.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_cpw1 (syn_cpw1 Q))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_Q,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cwpppowset2fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ (Q).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_Q, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (syn_cnc (syn_cpw (syn_cpw C))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowset2fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_y_not_Q, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cnc (syn_cpw (syn_cpw C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_y_not_C,
          not_false_eq_true])
  have p0000 := @g_wpppowset2fnfnndv
  have p0001 := @g_ssv (syn_cpw1 Q)
  have p0002 := @g_pw1ss (syn_cpw1 Q) (syn_cvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwpppowset2fn) (syn_cpw1 (syn_cvv)))
      (syn_wss (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cvv))) p0000 p0003
  have p0005 :=
    @g_fvelimab x (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cpw1 Q)) (.cv y) (syn_cwpppowset2fn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_biimpi (.classMem (.cv y) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_wrex x (syn_cpw1 (syn_cpw1 Q))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      p0006
  have p0008 :=
    @g_simpr (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))
  have p0009 :=
    @g_simpl (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))
  have p0010 := @g_ssv Q
  have p0011 := @g_pw1ss Q (syn_cvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @g_pw1ss (syn_cpw1 Q) (syn_cpw1 (syn_cvv))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_sseli (syn_cpw1 (syn_cpw1 Q)) (syn_cpw1 (syn_cpw1 (syn_cvv))) (.cv x) p0014
  have p0016 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0009 p0015
  have p0017 := @g_wpppowset2fnvalimpndv x
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x))
        (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))))
      p0016 p0017
  have p0020 := @g_fdcolcodearg Q x dv_cache_0004
  have p0021 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
        (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x)))))))
      p0009 p0020
  have p0022 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
      (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x))))))
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
        (.classEq (.cv x) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv x)))))))
      (.classMem (syn_cuni (syn_cuni (.cv x))) Q) p0021 p0022
  have p0024 :=
    @g_sseli Q (syn_cnc C) (syn_cuni (syn_cuni (.cv x))) hyp_wpppowset2imssndv_2
  have p0025 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (syn_cuni (syn_cuni (.cv x))) Q)
      (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C)) p0023 p0024
  have p0026 := @g_elnc (syn_cuni (syn_cuni (.cv x))) C
  have p0027 :=
    @g_sylib
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (syn_cuni (syn_cuni (.cv x))) (syn_cnc C))
      (syn_wbr (syn_cuni (syn_cuni (.cv x))) (syn_cen) C) p0025 p0026
  have p0028 := @g_enpw (syn_cuni (syn_cuni (.cv x))) C
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (syn_wbr (syn_cuni (syn_cuni (.cv x))) (syn_cen) C)
      (syn_wbr (syn_cpw (syn_cuni (syn_cuni (.cv x)))) (syn_cen) (syn_cpw C)) p0027 p0028
  have p0030 := @g_enpw (syn_cpw (syn_cuni (syn_cuni (.cv x)))) (syn_cpw C)
  have p0031 :=
    @g_syl
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (syn_wbr (syn_cpw (syn_cuni (syn_cuni (.cv x)))) (syn_cen) (syn_cpw C))
      (syn_wbr (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cen)
        (syn_cpw (syn_cpw C)))
      p0029 p0030
  have p0032 :=
    @g_elnc (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cpw (syn_cpw C))
  have p0033 :=
    @g_sylibr
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (syn_wbr (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cen)
        (syn_cpw (syn_cpw C)))
      (.classMem (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x)))))
        (syn_cnc (syn_cpw (syn_cpw C))))
      p0031 p0032
  have p0034 :=
    @g_eqeltrd
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (syn_cfv (syn_cwpppowset2fn) (.cv x))
      (syn_cpw (syn_cpw (syn_cuni (syn_cuni (.cv x))))) (syn_cnc (syn_cpw (syn_cpw C)))
      p0018 p0033
  have p0035 :=
    @g_eqeltrrd
      (syn_wa (.classMem (.cv x) (syn_cpw1 (syn_cpw1 Q)))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y) (syn_cnc (syn_cpw (syn_cpw C))) p0008
      p0034
  have p0036 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y))
      (.classMem (.cv y) (syn_cnc (syn_cpw (syn_cpw C)))) x (syn_cpw1 (syn_cpw1 Q))
      dv_cache_0005 p0035
  have p0037 :=
    @g_syl (.classMem (.cv y) (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))))
      (syn_wrex x (syn_cpw1 (syn_cpw1 Q))
        (.classEq (syn_cfv (syn_cwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv y) (syn_cnc (syn_cpw (syn_cpw C)))) p0007 p0036
  have p0038 :=
    @g_ssriv y (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))
      (syn_cnc (syn_cpw (syn_cpw C))) dv_cache_0006 dv_cache_0007 p0037
  exact p0038

@[expose]
noncomputable def g_sif1mapndv (A : Class) (B : Class) (F : Class)
    (hyp_sif1mapndv_1 : Nominal.NPrf (syn_wf1 F A B)) :
    Nominal.NPrf (syn_wf1 (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) :=
  by
  have p0000 := @g_f1f A B F
  have p0001 := Nominal.mp hyp_sif1mapndv_1 p0000
  have p0002 := @g_sifmap A B F
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0005 :=
    @g_mpbi (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
      hyp_sif1mapndv_1 p0004
  have p0006 := @g_simpri (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0005
  have p0007 := @g_funsi (syn_ccnv F)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_cnvsi F
  have p0010 := @g_funeqi (syn_ccnv (syn_csi F)) (syn_csi (syn_ccnv F)) p0009
  have p0011 :=
    @g_mpbir (syn_wfun (syn_ccnv (syn_csi F))) (syn_wfun (syn_csi (syn_ccnv F))) p0008
      p0010
  have p0012 :=
    @g_pm3_2i (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))
      (syn_wfun (syn_ccnv (syn_csi F))) p0003 p0011
  have p0013 := (Nominal.biimpRefl (syn_wf1 (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)))
  have p0014 :=
    @g_mpbir (syn_wf1 (syn_csi F) (syn_cpw1 A) (syn_cpw1 B))
      (syn_wa (syn_wf (syn_csi F) (syn_cpw1 A) (syn_cpw1 B)) (syn_wfun (syn_ccnv (syn_csi F))))
      p0012 p0013
  exact p0014

@[expose]
noncomputable def g_wppcardt2fnf1ndv :
    Nominal.NPrf
      (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs)) :=
  by
  have p0000 := @g_wppcardtfnf1ndv
  have p0002 := @g_sif1mapndv (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) p0000
  have p0003 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
      (syn_wf1 (syn_csi (syn_cwppcardtfn)) (syn_cpw1 (syn_cpw1 (syn_cncs)))
        (syn_cpw1 (syn_cncs)))
      p0000 p0002
  have p0004 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs)) (syn_cncs)
      (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := (Nominal.classEqRefl (syn_cwppcardt2fn))
  have p0007 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbir (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf1 (syn_ccom (syn_cwppcardtfn) (syn_csi (syn_cwppcardtfn)))
        (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      p0005 p0008
  exact p0009

@[expose]
noncomputable def g_wppcardt4fnf1ndv :
    Nominal.NPrf
      (syn_wf1 (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
        (syn_cncs)) :=
  by
  have p0000 := @g_wppcardt2fnf1ndv
  have p0002 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn) p0000
  have p0003 :=
    @g_sif1mapndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))) (syn_cpw1 (syn_cncs))
      (syn_csi (syn_cwppcardt2fn)) p0002
  have p0004 :=
    @g_pm3_2i (syn_wf1 (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf1 (syn_csi (syn_csi (syn_cwppcardt2fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0000 p0003
  have p0005 :=
    @g_f1co (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt2fn)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := (Nominal.classEqRefl (syn_cwppcardt4fn))
  have p0008 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_mpbir
      (syn_wf1 (syn_cwppcardt4fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
        (syn_cncs))
      (syn_wf1 (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt2fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs))
      p0006 p0009
  exact p0010

@[expose]
noncomputable def g_wppfamilyrep2fnexndv :
    Nominal.NPrf (.classMem (syn_cwppfamilyrep2fn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppfamilyrep2fn))
  have p0001 := @g_vvex
  have p0002 := @g_fdpointrelex (syn_cvv) p0001
  have p0003 := @g_imageex (syn_cfdpointrel (syn_cvv)) p0002
  have p0004 :=
    @g_eqeltri (syn_cwppfamilyrep2fn) (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_cvv)
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_wppfamilyrep2fnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv)) :=
  by
  have p0000 := @g_vvex
  have p0001 := @g_fdpointrelex (syn_cvv) p0000
  have p0002 := @g_wppimagefn (syn_cfdpointrel (syn_cvv)) p0001
  have p0003 := (Nominal.classEqRefl (syn_cwppfamilyrep2fn))
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_cwppfamilyrep2fn) (syn_cimage (syn_cfdpointrel (syn_cvv)))
      p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wfn (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_cvv)) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_wppfamilyrep2fnvalndv (Q : Class)
    (hyp_wppfamilyrep2fnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q)))
        (syn_cpw1 (syn_cpw1 Q))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppfamilyrep2fn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppfamilyrep2fn)
      (syn_cimage (syn_cfdpointrel (syn_cvv))) p0000
  have p0002 := @g_vvex
  have p0003 := @g_fdpointrelex (syn_cvv) p0002
  have p0004 := @g_snex (syn_csn Q)
  have p0005 := @g_fvimagecl (syn_csn (syn_csn Q)) (syn_cfdpointrel (syn_cvv)) p0003 p0004
  have p0006 := @g_fdpointimagevvdndv Q
  have p0007 := Nominal.mp hyp_wppfamilyrep2fnvalndv_1 p0006
  have p0008 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_csn (syn_csn Q)))
      (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn Q))) (syn_cpw1 (syn_cpw1 Q))
      p0005 p0007
  have p0009 :=
    @g_eqtri (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_cimage (syn_cfdpointrel (syn_cvv))) (syn_csn (syn_csn Q)))
      (syn_cpw1 (syn_cpw1 Q)) p0001 p0008
  exact p0009

@[expose]
noncomputable def g_wppdirecte2famfnexndv :
    Nominal.NPrf (.classMem (syn_cwppdirecte2famfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppdirecte2famfn))
  have p0001 := @g_wpppowset2fnexndv
  have p0002 := @g_imageex (syn_cwpppowset2fn) p0001
  have p0003 := @g_wppfamilyrep2fnexndv
  have p0004 :=
    @g_coex (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_cwppdirecte2famfn)
      (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_cvv) p0000
      p0004
  exact p0005

@[expose]
noncomputable def g_wppdirecte2famfnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv)) :=
  by
  have p0000 := @g_wpppowset2fnexndv
  have p0001 := @g_wppimagefn (syn_cwpppowset2fn) p0000
  have p0002 := @g_wppfamilyrep2fnfnndv
  have p0003 := @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpppowset2fn)) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := (Nominal.classEqRefl (syn_cwppdirecte2famfn))
  have p0009 :=
    @g_fneq1i (syn_cvv) (syn_cwppdirecte2famfn)
      (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) p0008
  have p0010 :=
    @g_mpbir (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv))
      (syn_wfn (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) (syn_cvv))
      p0007 p0009
  exact p0010

@[expose]
noncomputable def g_wppdirecte2famfnvalndv (Q : Class)
    (hyp_wppdirecte2famfnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn Q)))
        (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppdirecte2famfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppdirecte2famfn)
      (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn)) p0000
  have p0002 := @g_wppfamilyrep2fnfnndv
  have p0003 := @g_snex (syn_csn Q)
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (.classMem (syn_csn (syn_csn Q)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_csn Q)) (syn_cimage (syn_cwpppowset2fn))
      (syn_cwppfamilyrep2fn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_wppfamilyrep2fnvalndv Q hyp_wppdirecte2famfnvalndv_1
  have p0008 :=
    @g_fveq2i (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q)))
      (syn_cpw1 (syn_cpw1 Q)) (syn_cimage (syn_cwpppowset2fn)) p0007
  have p0009 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn Q)))
      (syn_cfv (syn_cimage (syn_cwpppowset2fn))
        (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn Q))))
      (syn_cfv (syn_cimage (syn_cwpppowset2fn)) (syn_cpw1 (syn_cpw1 Q))) p0006 p0008
  have p0010 := @g_wpppowset2fnexndv
  have p0011 := @g_pw1ex Q hyp_wppdirecte2famfnvalndv_1
  have p0012 := @g_pw1ex (syn_cpw1 Q) p0011
  have p0013 := @g_fvimagecl (syn_cpw1 (syn_cpw1 Q)) (syn_cwpppowset2fn) p0010 p0012
  have p0014 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn Q)))
      (syn_cfv (syn_cimage (syn_cwpppowset2fn)) (syn_cpw1 (syn_cpw1 Q)))
      (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) p0009 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpppowset2fn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn Q)))
      (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 Q))) p0001 p0014
  exact p0015

@[expose]
noncomputable def g_wppdirecth1famfnexndv :
    Nominal.NPrf (.classMem (syn_cwppdirecth1famfn) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppdirecth1famfn))
  have p0001 := @g_wpplitphnordpointfnexndv
  have p0002 := @g_imageex (syn_cwpplitphnordpointfn) p0001
  have p0003 := @g_wppfamilyrep2fnexndv
  have p0004 :=
    @g_coex (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn) p0002 p0003
  have p0005 := @g_wppdirecte2famfnexndv
  have p0006 := @g_siex (syn_cwppdirecte2famfn) p0005
  have p0007 := @g_siex (syn_csi (syn_cwppdirecte2famfn)) p0006
  have p0008 :=
    @g_coex (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecte2famfn))) p0004 p0007
  have p0009 :=
    @g_eqeltri (syn_cwppdirecth1famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecte2famfn))))
      (syn_cvv) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_wppdirecth1famfnfnndv :
    Nominal.NPrf (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv)))) :=
  by
  have p0000 := @g_wpplitphnordpointfnexndv
  have p0001 := @g_wppimagefn (syn_cwpplitphnordpointfn) p0000
  have p0002 := @g_wppfamilyrep2fnfnndv
  have p0003 := @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn))
      (syn_cwppfamilyrep2fn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_wppdirecte2famfnfnndv
  have p0009 := @g_dffn2 (syn_cvv) (syn_cwppdirecte2famfn)
  have p0010 :=
    @g_mpbi (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv))
      (syn_wf (syn_cwppdirecte2famfn) (syn_cvv) (syn_cvv)) p0008 p0009
  have p0011 := @g_sifmap (syn_cvv) (syn_cvv) (syn_cwppdirecte2famfn)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecte2famfn))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
      (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0018 :=
    @g_mpbi
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
        (syn_cvv))
      p0016 p0017
  have p0019 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cvv))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
        (syn_cvv))
      p0007 p0018
  have p0020 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cvv)))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := (Nominal.classEqRefl (syn_cwppdirecth1famfn))
  have p0023 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecte2famfn))))
      p0022
  have p0024 :=
    @g_mpbir (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wfn (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      p0021 p0023
  exact p0024

@[expose]
noncomputable def g_wppdirecth1famfnvalndv (Q : Class)
    (hyp_wppdirecth1famfnvalndv_1 : Nominal.NPrf (.classMem Q (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn Q)))
        (syn_cima (syn_cwpplitphnordpointfn)
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppdirecth1famfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppdirecth1famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecte2famfn))))
      p0000
  have p0002 := @g_wppdirecte2famfnfnndv
  have p0003 := @g_dffn2 (syn_cvv) (syn_cwppdirecte2famfn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppdirecte2famfn) (syn_cvv))
      (syn_wf (syn_cwppdirecte2famfn) (syn_cvv) (syn_cvv)) p0002 p0003
  have p0005 := @g_sifmap (syn_cvv) (syn_cvv) (syn_cwppdirecte2famfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_sifmap (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_cwppdirecte2famfn))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))
      (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_snelpw1 Q (syn_cvv)
  have p0012 :=
    @g_mpbir (.classMem (syn_csn Q) (syn_cpw1 (syn_cvv))) (.classMem Q (syn_cvv))
      hyp_wppdirecth1famfnvalndv_1 p0011
  have p0013 := @g_snelpw1 (syn_csn Q) (syn_cpw1 (syn_cvv))
  have p0014 :=
    @g_mpbir (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (.classMem (syn_csn Q) (syn_cpw1 (syn_cvv))) p0012 p0013
  have p0015 :=
    @g_pm3_2i
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0010 p0014
  have p0016 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csn (syn_csn Q))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecte2famfn)))
  have p0017 := Nominal.mp p0015 p0016
  have p0025 :=
    @g_sifvald (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csn Q)
      (syn_csi (syn_cwppdirecte2famfn)) p0006
  have p0026 := Nominal.mp p0012 p0025
  have p0030 := @g_sifvald (syn_cvv) (syn_cvv) Q (syn_cwppdirecte2famfn) p0004
  have p0031 := Nominal.mp hyp_wppdirecth1famfnvalndv_1 p0030
  have p0032 :=
    @g_sneqi (syn_cfv (syn_csi (syn_cwppdirecte2famfn)) (syn_csn Q))
      (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)) p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_csn (syn_csn Q)))
      (syn_csn (syn_cfv (syn_csi (syn_cwppdirecte2famfn)) (syn_csn Q)))
      (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))) p0026 p0032
  have p0034 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_csn (syn_csn Q)))
      (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) p0033
  have p0035 :=
    @g_eqtri
      (syn_cfv (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cfv (syn_csi (syn_csi (syn_cwppdirecte2famfn))) (syn_csn (syn_csn Q))))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))))
      p0017 p0034
  have p0036 := @g_wppfamilyrep2fnfnndv
  have p0037 := @g_snex (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (.classMem (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))) (syn_cvv)) p0036
      p0037
  have p0039 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))
      (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0040 := Nominal.mp p0038 p0039
  have p0041 := @g_fvex Q (syn_cwppdirecte2famfn)
  have p0042 := @g_wppfamilyrep2fnvalndv (syn_cfv (syn_cwppdirecte2famfn) Q) p0041
  have p0043 :=
    @g_fveq2i
      (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))
      (syn_cimage (syn_cwpplitphnordpointfn)) p0042
  have p0044 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))))
      (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cfv (syn_cwppfamilyrep2fn)
          (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q)))))
      (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))
      p0040 p0043
  have p0045 := @g_wpplitphnordpointfnexndv
  have p0047 := @g_pw1ex (syn_cfv (syn_cwppdirecte2famfn) Q) p0041
  have p0048 := @g_pw1ex (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)) p0047
  have p0049 :=
    @g_fvimagecl (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q)))
      (syn_cwpplitphnordpointfn) p0045 p0048
  have p0050 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))))
      (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))
      (syn_cima (syn_cwpplitphnordpointfn)
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))
      p0044 p0049
  have p0051 :=
    @g_eqtri
      (syn_cfv (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecte2famfn) Q))))
      (syn_cima (syn_cwpplitphnordpointfn)
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))
      p0035 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecte2famfn)))) (syn_csn (syn_csn Q)))
      (syn_cima (syn_cwpplitphnordpointfn)
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) Q))))
      p0001 p0051
  exact p0052

@[expose]
noncomputable def g_wppdirecth2famfnvalndv (Q : Class)
    (hyp_wppdirecth2famfnvalndv_1 :
      Nominal.NPrf (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cvv))))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppdirecth2famfn) (syn_csn (syn_csn Q)))
        (syn_cima (syn_cwpplitphnordpointfn)
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppdirecth2famfn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn Q)) (syn_cwppdirecth2famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
      p0000
  have p0002 := @g_wppdirecth1famfnfnndv
  have p0003 := @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0002
      p0003
  have p0005 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv))
      (syn_csi (syn_cwppdirecth1famfn))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @g_snelpw1 Q (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0012 :=
    @g_mpbir (.classMem (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cvv)))) hyp_wppdirecth2famfnvalndv_1 p0011
  have p0013 := @g_snelpw1 (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0014 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (.classMem (syn_csn Q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0012 p0013
  have p0015 :=
    @g_pm3_2i
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (.classMem (syn_csn (syn_csn Q)) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0010 p0014
  have p0016 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_csn (syn_csn Q))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0017 := Nominal.mp p0015 p0016
  have p0025 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv)) (syn_csn Q)
      (syn_csi (syn_cwppdirecth1famfn)) p0006
  have p0026 := Nominal.mp p0012 p0025
  have p0030 :=
    @g_sifvald (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) Q (syn_cwppdirecth1famfn) p0004
  have p0031 := Nominal.mp hyp_wppdirecth2famfnvalndv_1 p0030
  have p0032 :=
    @g_sneqi (syn_cfv (syn_csi (syn_cwppdirecth1famfn)) (syn_csn Q))
      (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)) p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_csn (syn_csn Q)))
      (syn_csn (syn_cfv (syn_csi (syn_cwppdirecth1famfn)) (syn_csn Q)))
      (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))) p0026 p0032
  have p0034 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_csn (syn_csn Q)))
      (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)) p0033
  have p0035 :=
    @g_eqtri
      (syn_cfv (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cfv (syn_csi (syn_csi (syn_cwppdirecth1famfn))) (syn_csn (syn_csn Q))))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))))
      p0017 p0034
  have p0036 := @g_wppfamilyrep2fnfnndv
  have p0037 := @g_snex (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (.classMem (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))) (syn_cvv)) p0036
      p0037
  have p0039 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))
      (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn)
  have p0040 := Nominal.mp p0038 p0039
  have p0041 := @g_fvex Q (syn_cwppdirecth1famfn)
  have p0042 := @g_wppfamilyrep2fnvalndv (syn_cfv (syn_cwppdirecth1famfn) Q) p0041
  have p0043 :=
    @g_fveq2i
      (syn_cfv (syn_cwppfamilyrep2fn) (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))
      (syn_cimage (syn_cwpplitphnordpointfn)) p0042
  have p0044 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))))
      (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cfv (syn_cwppfamilyrep2fn)
          (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q)))))
      (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))
      p0040 p0043
  have p0045 := @g_wpplitphnordpointfnexndv
  have p0047 := @g_pw1ex (syn_cfv (syn_cwppdirecth1famfn) Q) p0041
  have p0048 := @g_pw1ex (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)) p0047
  have p0049 :=
    @g_fvimagecl (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q)))
      (syn_cwpplitphnordpointfn) p0045 p0048
  have p0050 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))))
      (syn_cfv (syn_cimage (syn_cwpplitphnordpointfn))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))
      (syn_cima (syn_cwpplitphnordpointfn)
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))
      p0044 p0049
  have p0051 :=
    @g_eqtri
      (syn_cfv (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csn (syn_csn (syn_cfv (syn_cwppdirecth1famfn) Q))))
      (syn_cima (syn_cwpplitphnordpointfn)
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))
      p0035 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_cwppdirecth2famfn) (syn_csn (syn_csn Q)))
      (syn_cfv (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn)))) (syn_csn (syn_csn Q)))
      (syn_cima (syn_cwpplitphnordpointfn)
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn) Q))))
      p0001 p0051
  exact p0052

@[expose]
noncomputable def g_wppconcrete6codefnvalndv (X : Class)
    (hyp_wppconcrete6codefnvalndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cfv (syn_cwppconcrete6codefn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppconcrete6codefn))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_cwppconcrete6codefn) (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
      p0000
  have p0002 := @g_wpplitphnordpointfnexndv
  have p0003 := @g_wppimagefn (syn_cwpplitphnordpointfn) p0002
  have p0004 := @g_wppfamilyrep2fnfnndv
  have p0005 := @g_dffn2 (syn_cvv) (syn_cwppfamilyrep2fn)
  have p0006 :=
    @g_mpbi (syn_wfn (syn_cwppfamilyrep2fn) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cvv))
      (syn_wf (syn_cwppfamilyrep2fn) (syn_cvv) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnfco (syn_cvv) (syn_cvv) (syn_cimage (syn_cwpplitphnordpointfn))
      (syn_cwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @g_wppdirecth1famfnfnndv
  have p0011 := @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cwppdirecth1famfn)
  have p0012 :=
    @g_mpbi (syn_wfn (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wf (syn_cwppdirecth1famfn) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv)) p0010
      p0011
  have p0013 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cvv) (syn_cwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cvv))
      (syn_csi (syn_cwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_dffn2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0020 :=
    @g_mpbi
      (syn_wfn (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0018 p0019
  have p0021 :=
    @g_pm3_2i
      (syn_wfn (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_cvv))
      (syn_wf (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cvv))
      p0009 p0020
  have p0022 :=
    @g_fnfco (syn_cvv) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
      (syn_csi (syn_csi (syn_cwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (syn_cwppdirecth2famfn))
  have p0025 :=
    @g_fneq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_cwppdirecth2famfn)
      (syn_ccom (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
        (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
      p0024
  have p0026 :=
    @g_mpbir
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (syn_wfn (syn_ccom
          (syn_ccom (syn_cimage (syn_cwpplitphnordpointfn)) (syn_cwppfamilyrep2fn))
          (syn_csi (syn_csi (syn_cwppdirecth1famfn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0023 p0025
  have p0027 := @g_snex (syn_csn (syn_cnc X))
  have p0028 := @g_snelpw1 (syn_csn (syn_csn (syn_cnc X))) (syn_cvv)
  have p0029 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv)))
      (.classMem (syn_csn (syn_csn (syn_cnc X))) (syn_cvv)) p0027 p0028
  have p0030 := @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))
  have p0031 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))
        (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_cnc X)))) (syn_cpw1 (syn_cvv))) p0029
      p0030
  have p0032 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0033 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))
        (syn_cpw1 (syn_cpw1 (syn_cvv))))
      p0031 p0032
  have p0034 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0035 :=
    @g_mpbir
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      p0033 p0034
  have p0036 :=
    @g_pm3_2i
      (syn_wfn (syn_cwppdirecth2famfn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
      p0026 p0035
  have p0037 :=
    @g_fvco2 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn)
  have p0038 := Nominal.mp p0036 p0037
  have p0044 :=
    @g_wppdirecth2famfnvalndv (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))) p0031
  have p0045 :=
    @g_fveq2i
      (syn_cfv (syn_cwppdirecth2famfn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_cwppdirecth1famfn)
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))))
      (syn_cimage (syn_cen)) p0044
  have p0046 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_cfv (syn_cimage (syn_cen)) (syn_cfv (syn_cwppdirecth2famfn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))))
      (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1
              (syn_cfv (syn_cwppdirecth1famfn)
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))))
      p0038 p0045
  have p0048 := @g_wppdirecth1famfnvalndv (syn_csn (syn_csn (syn_cnc X))) p0027
  have p0049 := @g_ncex X
  have p0050 := @g_wppdirecte2famfnvalndv (syn_cnc X) p0049
  have p0052 := @g_wpppowset2imexndv (syn_cnc X) p0049
  have p0053 :=
    @g_eqeltri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))
      (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))) (syn_cvv) p0050
      p0052
  have p0054 :=
    @g_wpplitphnordimexndv
      (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) p0053
  have p0055 :=
    @g_eqeltri
      (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
      (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1
          (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_cvv) p0048 p0054
  have p0062 := @g_enrflx X hyp_wppconcrete6codefnvalndv_1
  have p0063 := @g_elnc X X
  have p0064 := @g_mpbir (.classMem X (syn_cnc X)) (syn_wbr X (syn_cen) X) p0062 p0063
  have p0065 := @g_wpppowset2imcanndv X (syn_cnc X) p0049 p0064
  have p0068 :=
    @g_eleq2i (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))
      (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X))))
      (syn_cpw (syn_cpw X)) p0050
  have p0069 :=
    @g_mpbir
      (.classMem (syn_cpw (syn_cpw X))
        (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))))
      (.classMem (syn_cpw (syn_cpw X))
        (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X)))))
      p0065 p0068
  have p0070 :=
    @g_wpplitphnordimcanndv (syn_cpw (syn_cpw X))
      (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) p0053 p0069
  have p0073 :=
    @g_eleq2i
      (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
      (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1
          (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_chnord (syn_cpw (syn_cpw X))) p0048
  have p0074 :=
    @g_mpbir
      (.classMem (syn_chnord (syn_cpw (syn_cpw X))) (syn_cfv (syn_cwppdirecth1famfn)
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X)))))))
      (.classMem (syn_chnord (syn_cpw (syn_cpw X))) (syn_cima (syn_cwpplitphnordpointfn)
          (syn_cpw1 (syn_cpw1
              (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))))))
      p0070 p0073
  have p0085 := @g_ssid (syn_cnc X)
  have p0086 := @g_wpppowset2imssndv X (syn_cnc X) p0049 p0085
  have p0087 :=
    @g_eqsstri (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X))))
      (syn_cima (syn_cwpppowset2fn) (syn_cpw1 (syn_cpw1 (syn_cnc X))))
      (syn_cnc (syn_cpw (syn_cpw X))) p0050 p0086
  have p0088 :=
    @g_wpplitphnordimssndv (syn_cpw (syn_cpw X))
      (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))) p0053 p0087
  have p0089 :=
    @g_eqsstri
      (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
      (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1
          (syn_cpw1 (syn_cfv (syn_cwppdirecte2famfn) (syn_csn (syn_csn (syn_cnc X)))))))
      (syn_cnc (syn_chnord (syn_cpw (syn_cpw X)))) p0048 p0088
  have p0090 :=
    @g_wpplitphnordcardvalndv (syn_chnord (syn_cpw (syn_cpw X)))
      (syn_cfv (syn_cwppdirecth1famfn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))
      p0055 p0074 p0089
  have p0091 :=
    @g_eqtri
      (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_cfv (syn_cimage (syn_cen)) (syn_cima (syn_cwpplitphnordpointfn) (syn_cpw1 (syn_cpw1
              (syn_cfv (syn_cwppdirecth1famfn)
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) p0046 p0090
  have p0092 :=
    @g_eqtri
      (syn_cfv (syn_cwppconcrete6codefn)
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_cfv (syn_ccom (syn_cimage (syn_cen)) (syn_cwppdirecth2famfn))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_cnc X))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) p0001 p0091
  exact p0092

@[expose]
noncomputable def g_wppcardt6fnmapndv :
    Nominal.NPrf
      (syn_wf (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cncs)) :=
  by
  have p0000 := @g_wppcardt2fnmapndv
  have p0001 := @g_wppcardt4fnmapndv
  have p0002 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (syn_cncs)
      (syn_cwppcardt4fn)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
      (syn_cpw1 (syn_cncs)) (syn_csi (syn_cwppcardt4fn))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf (syn_cwppcardt2fn) (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs))
      (syn_wf (syn_csi (syn_csi (syn_cwppcardt4fn)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
        (syn_cpw1 (syn_cpw1 (syn_cncs))))
      p0000 p0005
  have p0007 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cpw1 (syn_cpw1 (syn_cncs))) (syn_cncs) (syn_cwppcardt2fn)
      (syn_csi (syn_csi (syn_cwppcardt4fn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (syn_cwppcardt6fn))
  have p0010 :=
    @g_feq1i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))
      (syn_cncs) (syn_cwppcardt6fn)
      (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn)))) p0009
  have p0011 :=
    @g_mpbir
      (syn_wf (syn_cwppcardt6fn)
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      (syn_wf (syn_ccom (syn_cwppcardt2fn) (syn_csi (syn_csi (syn_cwppcardt4fn))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs))
      p0008 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end
