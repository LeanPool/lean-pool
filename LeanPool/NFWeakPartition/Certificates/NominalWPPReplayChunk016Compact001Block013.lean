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

/-- Checked nominal proof certificate identified upstream as `g_wppcardt4fnvalsingndv`. -/
@[expose]
noncomputable def gWppcardt4fnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (synCncs))
        (.classEq (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))
          (synCtc (synCtc (synCtc (synCtc D)))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardt4fn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn (synCsn (synCsn D)))) (synCwppcardt4fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn)))) p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))
        (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
          (synCsn (synCsn (synCsn (synCsn D))))))
      (.classMem D (synCncs)) p0001
  have p0003 := @gWppcardt2fnmapndv
  have p0004 := @gSifmap (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCncs))
      (synCsi (synCwppcardt2fn))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gA1i
      (synWf (synCsi (synCsi (synCwppcardt2fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCpw1 (synCpw1 (synCncs))))
      (.classMem D (synCncs)) p0007
  have p0009 := @gSnelpw1 D (synCncs)
  have p0010 :=
    @gBiimpri (.classMem (synCsn D) (synCpw1 (synCncs))) (.classMem D (synCncs))
      p0009
  have p0011 := @gSnelpw1 (synCsn D) (synCpw1 (synCncs))
  have p0012 :=
    @gBiimpri (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn D) (synCpw1 (synCncs))) p0011
  have p0013 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCsn D) (synCpw1 (synCncs)))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))) p0010 p0012
  have p0014 := @gSnelpw1 (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))
  have p0015 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs)))) p0014
  have p0016 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0013 p0015
  have p0017 :=
    @gSnelpw1 (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs))))
  have p0018 :=
    @gBiimpri
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      p0017
  have p0019 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0016 p0018
  have p0020 :=
    @gJca (.classMem D (synCncs))
      (synWf (synCsi (synCsi (synCwppcardt2fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCpw1 (synCpw1 (synCncs))))
      (.classMem (synCsn (synCsn (synCsn (synCsn D))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      p0008 p0019
  have p0021 :=
    @gFvco3 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCpw1 (synCpw1 (synCncs))) (synCsn (synCsn (synCsn (synCsn D))))
      (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn)))
  have p0022 :=
    @gSyl (.classMem D (synCncs))
      (synWa (synWf (synCsi (synCsi (synCwppcardt2fn)))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
          (synCpw1 (synCpw1 (synCncs)))) (.classMem (synCsn (synCsn (synCsn (synCsn D))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (.classEq (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
          (synCsn (synCsn (synCsn (synCsn D))))) (synCfv (synCwppcardt2fn)
          (synCfv (synCsi (synCsi (synCwppcardt2fn)))
            (synCsn (synCsn (synCsn (synCsn D)))))))
      p0020 p0021
  have p0034 :=
    @gSifvald (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCncs))
      (synCsn (synCsn (synCsn D))) (synCsi (synCwppcardt2fn)) p0005
  have p0035 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn (synCsn D))) (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (.classEq (synCfv (synCsi (synCsi (synCwppcardt2fn)))
          (synCsn (synCsn (synCsn (synCsn D)))))
        (synCsn (synCfv (synCsi (synCwppcardt2fn)) (synCsn (synCsn (synCsn D))))))
      p0016 p0034
  have p0042 :=
    @gSifvald (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCsn (synCsn D))
      (synCwppcardt2fn) p0003
  have p0043 :=
    @gSyl (.classMem D (synCncs))
      (.classMem (synCsn (synCsn D)) (synCpw1 (synCpw1 (synCncs))))
      (.classEq (synCfv (synCsi (synCwppcardt2fn)) (synCsn (synCsn (synCsn D))))
        (synCsn (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))))
      p0013 p0042
  have p0044 :=
    @gSneqd (.classMem D (synCncs))
      (synCfv (synCsi (synCwppcardt2fn)) (synCsn (synCsn (synCsn D))))
      (synCsn (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))) p0043
  have p0045 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCsi (synCsi (synCwppcardt2fn))) (synCsn (synCsn (synCsn (synCsn D)))))
      (synCsn (synCfv (synCsi (synCwppcardt2fn)) (synCsn (synCsn (synCsn D)))))
      (synCsn (synCsn (synCfv (synCwppcardt2fn) (synCsn (synCsn D))))) p0035 p0044
  have p0046 := @gWppcardt2fnvalsingndv D
  have p0047 :=
    @gSneqd (.classMem D (synCncs)) (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))
      (synCtc (synCtc D)) p0046
  have p0048 :=
    @gSneqd (.classMem D (synCncs))
      (synCsn (synCfv (synCwppcardt2fn) (synCsn (synCsn D))))
      (synCsn (synCtc (synCtc D))) p0047
  have p0049 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCsi (synCsi (synCwppcardt2fn))) (synCsn (synCsn (synCsn (synCsn D)))))
      (synCsn (synCsn (synCfv (synCwppcardt2fn) (synCsn (synCsn D)))))
      (synCsn (synCsn (synCtc (synCtc D)))) p0045 p0048
  have p0050 :=
    @gFveq2d (.classMem D (synCncs))
      (synCfv (synCsi (synCsi (synCwppcardt2fn))) (synCsn (synCsn (synCsn (synCsn D)))))
      (synCsn (synCsn (synCtc (synCtc D)))) (synCwppcardt2fn) p0049
  have p0051 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
        (synCsn (synCsn (synCsn (synCsn D)))))
      (synCfv (synCwppcardt2fn) (synCfv (synCsi (synCsi (synCwppcardt2fn)))
          (synCsn (synCsn (synCsn (synCsn D))))))
      (synCfv (synCwppcardt2fn) (synCsn (synCsn (synCtc (synCtc D))))) p0022 p0050
  have p0052 := @gTccl D
  have p0053 := @gTccl (synCtc D)
  have p0054 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCtc D) (synCncs))
      (.classMem (synCtc (synCtc D)) (synCncs)) p0052 p0053
  have p0055 := @gWppcardt2fnvalsingndv (synCtc (synCtc D))
  have p0056 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCtc (synCtc D)) (synCncs))
      (.classEq (synCfv (synCwppcardt2fn) (synCsn (synCsn (synCtc (synCtc D)))))
        (synCtc (synCtc (synCtc (synCtc D)))))
      p0054 p0055
  have p0057 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
        (synCsn (synCsn (synCsn (synCsn D)))))
      (synCfv (synCwppcardt2fn) (synCsn (synCsn (synCtc (synCtc D)))))
      (synCtc (synCtc (synCtc (synCtc D)))) p0051 p0056
  have p0058 :=
    @gEqtrd (.classMem D (synCncs))
      (synCfv (synCwppcardt4fn) (synCsn (synCsn (synCsn (synCsn D)))))
      (synCfv (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
        (synCsn (synCsn (synCsn (synCsn D)))))
      (synCtc (synCtc (synCtc (synCtc D)))) p0002 p0057
  exact p0058

/-- Checked nominal proof certificate identified upstream as `g_cnv2resndv`. -/
@[expose]
noncomputable def gCnv2resndv (A : Class) (B : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv) :
    Nominal.NPrf
      (.classEq (synCcnv (synCres (synCcnv (synCres R A)) B)) (synCin R (synCxp A B))) :=
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
  have dv_cache_0001 : x ∉ ((synCcnv (synCres (synCcnv (synCres R A)) B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCcnv (synCres (synCcnv (synCres R A)) B))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCin R (synCxp A B))).fv :=
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
  have dv_cache_0004 : y ∉ ((synCin R (synCxp A B))).fv :=
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
  have p0000 := @gBrcnv (.cv x) (.cv y) (synCres (synCcnv (synCres R A)) B)
  have p0001 := @gBrres (.cv y) (.cv x) (synCcnv (synCres R A)) B
  have p0002 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCres (synCcnv (synCres R A)) B)) (.cv y))
      (synWbr (.cv y) (synCres (synCcnv (synCres R A)) B) (.cv x))
      (synWa (synWbr (.cv y) (synCcnv (synCres R A)) (.cv x)) (.classMem (.cv y) B))
      p0000 p0001
  have p0003 := @gBrcnv (.cv y) (.cv x) (synCres R A)
  have p0004 :=
    @gAnbi1i (synWbr (.cv y) (synCcnv (synCres R A)) (.cv x))
      (synWbr (.cv x) (synCres R A) (.cv y)) (.classMem (.cv y) B) p0003
  have p0005 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCres (synCcnv (synCres R A)) B)) (.cv y))
      (synWa (synWbr (.cv y) (synCcnv (synCres R A)) (.cv x)) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) (synCres R A) (.cv y)) (.classMem (.cv y) B)) p0002 p0004
  have p0006 := @gBrres (.cv x) (.cv y) R A
  have p0007 :=
    @gAnbi1i (synWbr (.cv x) (synCres R A) (.cv y))
      (synWa (synWbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B)
      p0006
  have p0008 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCres (synCcnv (synCres R A)) B)) (.cv y))
      (synWa (synWbr (.cv x) (synCres R A) (.cv y)) (.classMem (.cv y) B))
      (synWa (synWa (synWbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B))
      p0005 p0007
  have p0009 :=
    @gAnass (synWbr (.cv x) R (.cv y)) (.classMem (.cv x) A) (.classMem (.cv y) B)
  have p0010 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCres (synCcnv (synCres R A)) B)) (.cv y))
      (synWa (synWa (synWbr (.cv x) R (.cv y)) (.classMem (.cv x) A)) (.classMem (.cv y) B))
      (synWa (synWbr (.cv x) R (.cv y)) (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      p0008 p0009
  have p0011 := @gBrxp (.cv x) (.cv y) A B
  have p0012 :=
    @gBicomi (synWbr (.cv x) (synCxp A B) (.cv y))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0011
  have p0013 :=
    @gAnbi2i (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (synWbr (.cv x) (synCxp A B) (.cv y)) (synWbr (.cv x) R (.cv y)) p0012
  have p0014 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCres (synCcnv (synCres R A)) B)) (.cv y))
      (synWa (synWbr (.cv x) R (.cv y)) (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) (synCxp A B) (.cv y))) p0010
      p0013
  have p0015 := @gBrin (.cv x) (.cv y) R (synCxp A B)
  have p0016 :=
    @gBicomi (synWbr (.cv x) (synCin R (synCxp A B)) (.cv y))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) (synCxp A B) (.cv y))) p0015
  have p0017 :=
    @gBitri (synWbr (.cv x) (synCcnv (synCres (synCcnv (synCres R A)) B)) (.cv y))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) (synCxp A B) (.cv y)))
      (synWbr (.cv x) (synCin R (synCxp A B)) (.cv y)) p0014 p0016
  have p0018 :=
    @gEqbrriv x y (synCcnv (synCres (synCcnv (synCres R A)) B))
      (synCin R (synCxp A B)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_cnvrngresndv`. -/
@[expose]
noncomputable def gCnvrngresndv (B : Class) (R : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCres (synCcnv R) B)) (synCin R (synCxp (synCvv) B))) :=
  by
  have dv_cache_0001 : Disjoint ((synCvv)).fv (R).fv := by
    exact
      (show Disjoint ((synCvv)).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
          exact (show Disjoint ((∅ : Finset Var)) ((R).fv) from (by simp))))
  have p0000 := @gResid R
  have p0001 := @gCnveqi (synCres R (synCvv)) R p0000
  have p0002 := @gReseq1i (synCcnv (synCres R (synCvv))) (synCcnv R) B p0001
  have p0003 :=
    @gCnveqi (synCres (synCcnv (synCres R (synCvv))) B) (synCres (synCcnv R) B)
      p0002
  have p0004 := @gCnv2resndv (synCvv) B R dv_cache_0001
  have p0005 :=
    @gEqtr3i (synCcnv (synCres (synCcnv (synCres R (synCvv))) B))
      (synCcnv (synCres (synCcnv R) B)) (synCin R (synCxp (synCvv) B)) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hwcodesunivndv`. -/
@[expose]
noncomputable def gHwcodesunivndv :
    Nominal.NPrf (.classEq (synChwcodes (synCvv)) (synCwe)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcodes (synCvv)))
  have p0001 := @gPwv
  have p0002 := @gXpeq2i (synCpw (synCvv)) (synCvv) (synCvv) p0001
  have p0003 := @gXpvv
  have p0004 :=
    @gEqtri (synCxp (synCvv) (synCpw (synCvv))) (synCxp (synCvv) (synCvv))
      (synCvv) p0002 p0003
  have p0005 :=
    @gIneq2i (synCxp (synCvv) (synCpw (synCvv))) (synCvv) (synCwe) p0004
  have p0006 := @gInv1 (synCwe)
  have p0007 :=
    @gEqtri (synCin (synCwe) (synCxp (synCvv) (synCpw (synCvv))))
      (synCin (synCwe) (synCvv)) (synCwe) p0005 p0006
  have p0008 :=
    @gEqtri (synChwcodes (synCvv))
      (synCin (synCwe) (synCxp (synCvv) (synCpw (synCvv)))) (synCwe) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hwcnunivrrndv`. -/
@[expose]
noncomputable def gHwcnunivrrndv (A : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)))
        (synChwcn A)) :=
  by
  have p0000 := @gCnvrngresndv (synCpw A) (synChwcn (synCvv))
  have p0001 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0002 :=
    @gIneq1i (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCxp (synCvv) (synCpw A)) p0001
  have p0003 := (Nominal.classEqRefl (synChwcodes (synCvv)))
  have p0004 := @gPwv
  have p0005 := @gXpeq2i (synCpw (synCvv)) (synCvv) (synCvv) p0004
  have p0006 := @gXpvv
  have p0007 :=
    @gEqtri (synCxp (synCvv) (synCpw (synCvv))) (synCxp (synCvv) (synCvv))
      (synCvv) p0005 p0006
  have p0008 :=
    @gIneq2i (synCxp (synCvv) (synCpw (synCvv))) (synCvv) (synCwe) p0007
  have p0009 := @gInv1 (synCwe)
  have p0010 :=
    @gEqtri (synCin (synCwe) (synCxp (synCvv) (synCpw (synCvv))))
      (synCin (synCwe) (synCvv)) (synCwe) p0008 p0009
  have p0011 :=
    @gEqtri (synChwcodes (synCvv))
      (synCin (synCwe) (synCxp (synCvv) (synCpw (synCvv)))) (synCwe) p0003 p0010
  have p0012 := @gIneq1i (synChwcodes (synCvv)) (synCwe) (synChwrels) p0011
  have p0013 :=
    @gIneq1i (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCin (synCwe) (synChwrels)) (synCxp (synCvv) (synCpw A)) p0012
  have p0014 :=
    @gEqtri (synCin (synChwcn (synCvv)) (synCxp (synCvv) (synCpw A)))
      (synCin (synCin (synChwcodes (synCvv)) (synChwrels)) (synCxp (synCvv) (synCpw A)))
      (synCin (synCin (synCwe) (synChwrels)) (synCxp (synCvv) (synCpw A))) p0002
      p0013
  have p0015 := @gIn32 (synCwe) (synChwrels) (synCxp (synCvv) (synCpw A))
  have p0016 :=
    @gEqtri (synCin (synChwcn (synCvv)) (synCxp (synCvv) (synCpw A)))
      (synCin (synCin (synCwe) (synChwrels)) (synCxp (synCvv) (synCpw A)))
      (synCin (synCin (synCwe) (synCxp (synCvv) (synCpw A))) (synChwrels)) p0014
      p0015
  have p0017 := (Nominal.classEqRefl (synChwcodes A))
  have p0018 :=
    @gEqcomi (synChwcodes A) (synCin (synCwe) (synCxp (synCvv) (synCpw A))) p0017
  have p0019 :=
    @gIneq1i (synCin (synCwe) (synCxp (synCvv) (synCpw A))) (synChwcodes A)
      (synChwrels) p0018
  have p0020 :=
    @gEqtri (synCin (synChwcn (synCvv)) (synCxp (synCvv) (synCpw A)))
      (synCin (synCin (synCwe) (synCxp (synCvv) (synCpw A))) (synChwrels))
      (synCin (synChwcodes A) (synChwrels)) p0016 p0019
  have p0021 := (Nominal.classEqRefl (synChwcn A))
  have p0022 := @gEqcomi (synChwcn A) (synCin (synChwcodes A) (synChwrels)) p0021
  have p0023 :=
    @gEqtri (synCin (synChwcn (synCvv)) (synCxp (synCvv) (synCpw A)))
      (synCin (synChwcodes A) (synChwrels)) (synChwcn A) p0020 p0022
  have p0024 :=
    @gEqtri (synCcnv (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)))
      (synCin (synChwcn (synCvv)) (synCxp (synCvv) (synCpw A))) (synChwcn A) p0000
      p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_hwnisogendrrndv`. -/
@[expose]
noncomputable def gHwnisogendrrndv (A : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCres (synCcnv
              (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
            (synChwcn A))) (synChwniso A)) :=
  by
  have dv_cache_0001 :
    Disjoint ((synChwcn A)).fv
      ((synCima (synChwgen) (synCxp (synChwbij) (synCvv)))).fv :=
    by
    exact
      (show Disjoint ((synChwcn A)).fv
          ((synCima (synChwgen) (synCxp (synChwbij) (synCvv)))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima];
          exact
            (show
              Disjoint ((A).fv)
                ((((synChwgen)).fv) ∪ (((synCxp (synChwbij) (synCvv))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((synChwgen)).fv) from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen];
                      exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))),
                  (show Disjoint ((A).fv) (((synCxp (synChwbij) (synCvv))).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp];
                      exact
                        (show Disjoint ((A).fv) ((((synChwbij)).fv) ∪ (((synCvv)).fv))
                          from
                          (Finset.disjoint_union_right.mpr
                            ⟨(show Disjoint ((A).fv) (((synChwbij)).fv) from
                                (by
                                  rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp)))),
                              (show Disjoint ((A).fv) (((synCvv)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp))))⟩))))⟩))))
  have p0000 :=
    @gCnv2resndv (synChwcn A) (synChwcn A)
      (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) dv_cache_0001
  have p0001 := (Nominal.classEqRefl (synChwniso A))
  have p0002 :=
    @gEqcomi (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      p0001
  have p0003 :=
    @gEqtri
      (synCcnv (synCres (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synChwniso A) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_wpppowsetfnexndv`. -/
@[expose]
noncomputable def gWpppowsetfnexndv :
    Nominal.NPrf (.classMem (synCwpppowsetfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0001 := @gSsetex
  have p0002 := @gCnvex (synCsset) p0001
  have p0003 := @gImageex (synCcnv (synCsset)) p0002
  have p0004 :=
    @gEqeltri (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) (synCvv) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wpppowsetfnfnndv`. -/
@[expose]
noncomputable def gWpppowsetfnfnndv :
    Nominal.NPrf (synWfn (synCwpppowsetfn) (synCvv)) :=
  by
  have p0000 := @gSsetex
  have p0001 := @gCnvex (synCsset) p0000
  have p0002 := @gWppimagefn (synCcnv (synCsset)) p0001
  have p0003 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0004 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0003
  have p0005 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wpppowsetfnvalndv`. -/
@[expose]
noncomputable def gWpppowsetfnvalndv (A : Class)
    (hyp_wpppowsetfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCwpppowsetfn) (synCsn A)) (synCpw A)) :=
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
  have dv_cache_0001 : x ∉ ((synCsset)).fv := by
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
  have p0000 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0001 :=
    @gFveq1i (synCsn A) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0000
  have p0002 := @gSsetex
  have p0003 := @gCnvex (synCsset) p0002
  have p0004 := @gSnex A
  have p0005 := @gFvimagecl (synCsn A) (synCcnv (synCsset)) p0003 p0004
  have p0006 := @gIniseg x (synCsset) A dv_cache_0001 dv_cache_0002
  have p0007 := @gVex x
  have p0008 := @gBrsset (.cv x) A p0007 hyp_wpppowsetfnvalndv_1
  have p0009 := @gAbbii (synWbr (.cv x) (synCsset) A) (synWss (.cv x) A) x p0008
  have p0010 :=
    @gEqtri (synCima (synCcnv (synCsset)) (synCsn A))
      (.cab x (synWbr (.cv x) (synCsset) A)) (.cab x (synWss (.cv x) A)) p0006 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw x A dv_cache_0002
  have p0012 := @gEqcomi (synCpw A) (.cab x (synWss (.cv x) A)) p0011
  have p0013 :=
    @gEqtri (synCima (synCcnv (synCsset)) (synCsn A)) (.cab x (synWss (.cv x) A))
      (synCpw A) p0010 p0012
  have p0014 :=
    @gEqtri (synCfv (synCimage (synCcnv (synCsset))) (synCsn A))
      (synCima (synCcnv (synCsset)) (synCsn A)) (synCpw A) p0005 p0013
  have p0015 :=
    @gEqtri (synCfv (synCwpppowsetfn) (synCsn A))
      (synCfv (synCimage (synCcnv (synCsset))) (synCsn A)) (synCpw A) p0001 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wpphwcnsetfnvalndv`. -/
@[expose]
noncomputable def gWpphwcnsetfnvalndv (A : Class)
    (hyp_wpphwcnsetfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCwpphwcnsetfn) (synCsn A)) (synChwcn A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0001 :=
    @gFveq1i (synCsn A) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0000
  have p0002 := @gLnimageresfnfn
  have p0003 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0004 := @gHwcodesunivndv
  have p0005 := @gWeex
  have p0006 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0004 p0005
  have p0007 := @gHwrelsex
  have p0008 := @gInex (synChwcodes (synCvv)) (synChwrels) p0006 p0007
  have p0009 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0003 p0008
  have p0010 := @gCnvex (synChwcn (synCvv)) p0009
  have p0011 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gSsetex
  have p0014 := @gCnvex (synCsset) p0013
  have p0015 := @gWppimagefn (synCcnv (synCsset)) p0014
  have p0016 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0017 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0016
  have p0018 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0015 p0017
  have p0019 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0012 p0018
  have p0020 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gInidm (synCvv)
  have p0023 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0022
  have p0024 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0021 p0023
  have p0025 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0002 p0024
  have p0026 := @gSnex A
  have p0027 :=
    @gPm32i
      (synWfn (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))) (synCvv))
      (.classMem (synCsn A) (synCvv)) p0025 p0026
  have p0028 :=
    @gFvco2 (synCvv) (synCsn A) (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
  have p0029 := Nominal.mp p0027 p0028
  have p0053 :=
    @gPm32i
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      (.classMem (synCsn A) (synCvv)) p0024 p0026
  have p0054 :=
    @gFvco2 (synCvv) (synCsn A) (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
  have p0055 := Nominal.mp p0053 p0054
  have p0073 :=
    @gFvtxpvv (synCsn A) (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
      (synCwpppowsetfn) p0012 p0018 p0026
  have p0083 := @gFvconst2 (synCvv) (synCcnv (synChwcn (synCvv))) (synCsn A) p0010
  have p0084 := Nominal.mp p0026 p0083
  have p0085 := @gWpppowsetfnvalndv A hyp_wpphwcnsetfnvalndv_1
  have p0086 :=
    @gOpeq12i
      (synCfv (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCsn A))
      (synCcnv (synChwcn (synCvv))) (synCfv (synCwpppowsetfn) (synCsn A))
      (synCpw A) p0084 p0085
  have p0087 :=
    @gEqtri
      (synCfv (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCsn A))
      (synCop (synCfv (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCsn A)) (synCfv (synCwpppowsetfn) (synCsn A)))
      (synCop (synCcnv (synChwcn (synCvv))) (synCpw A)) p0073 p0086
  have p0088 :=
    @gFveq2i
      (synCfv (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCsn A))
      (synCop (synCcnv (synChwcn (synCvv))) (synCpw A)) (synClnimageresfn) p0087
  have p0089 :=
    @gEqtri
      (synCfv (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))) (synCsn A))
      (synCfv (synClnimageresfn) (synCfv
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn)) (synCsn A)))
      (synCfv (synClnimageresfn) (synCop (synCcnv (synChwcn (synCvv))) (synCpw A)))
      p0055 p0088
  have p0098 := @gPwex A hyp_wpphwcnsetfnvalndv_1
  have p0099 :=
    @gLnimageresfnval (synCpw A) (synCcnv (synChwcn (synCvv))) p0010 p0098
  have p0100 :=
    @gEqtri
      (synCfv (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))) (synCsn A))
      (synCfv (synClnimageresfn) (synCop (synCcnv (synChwcn (synCvv))) (synCpw A)))
      (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)) p0089 p0099
  have p0101 :=
    @gFveq2i
      (synCfv (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))) (synCsn A))
      (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)) (synCimage (synCswap))
      p0100
  have p0102 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCsn A))
      (synCfv (synCimage (synCswap)) (synCfv (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn))) (synCsn A)))
      (synCfv (synCimage (synCswap)) (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)))
      p0029 p0101
  have p0112 := @gResex (synCcnv (synChwcn (synCvv))) (synCpw A) p0010 p0098
  have p0113 :=
    @gWppimageswapfv (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)) p0112
  have p0114 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCsn A))
      (synCfv (synCimage (synCswap)) (synCres (synCcnv (synChwcn (synCvv))) (synCpw A)))
      (synCcnv (synCres (synCcnv (synChwcn (synCvv))) (synCpw A))) p0102 p0113
  have p0115 := @gHwcnunivrrndv A
  have p0116 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCsn A))
      (synCcnv (synCres (synCcnv (synChwcn (synCvv))) (synCpw A))) (synChwcn A)
      p0114 p0115
  have p0117 :=
    @gEqtri (synCfv (synCwpphwcnsetfn) (synCsn A))
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCsn A))
      (synChwcn A) p0001 p0116
  exact p0117

/-- Checked nominal proof certificate identified upstream as `g_wpphwgendomfnvalndv`. -/
@[expose]
noncomputable def gWpphwgendomfnvalndv (A : Class)
    (hyp_wpphwgendomfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpphwgendomfn) (synCsn A))
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0001 :=
    @gFveq1i (synCsn A) (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      p0000
  have p0002 := @gHwgenex
  have p0003 := @gHwbijex
  have p0004 := @gVvex
  have p0005 := @gXpex (synChwbij) (synCvv) p0003 p0004
  have p0006 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0002 p0005
  have p0007 :=
    @gFnconstg (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCvv)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gImageswapfn
  have p0010 := @gLnimageresfnfn
  have p0011 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0012 := @gHwcodesunivndv
  have p0013 := @gWeex
  have p0014 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0012 p0013
  have p0015 := @gHwrelsex
  have p0016 := @gInex (synChwcodes (synCvv)) (synChwrels) p0014 p0015
  have p0017 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0011 p0016
  have p0018 := @gCnvex (synChwcn (synCvv)) p0017
  have p0019 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @gSsetex
  have p0022 := @gCnvex (synCsset) p0021
  have p0023 := @gWppimagefn (synCcnv (synCsset)) p0022
  have p0024 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0025 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0024
  have p0026 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0023 p0025
  have p0027 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0020 p0026
  have p0028 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @gInidm (synCvv)
  have p0031 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0030
  have p0032 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0029 p0031
  have p0033 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0010 p0032
  have p0034 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0009 p0033
  have p0035 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0036 :=
    @gFneq1i (synCvv) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0035
  have p0037 :=
    @gMpbir (synWfn (synCwpphwcnsetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCvv))
      p0034 p0036
  have p0038 :=
    @gPm32i
      (synWfn (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0008 p0037
  have p0039 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)
  have p0040 := Nominal.mp p0038 p0039
  have p0042 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0030
  have p0043 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      p0040 p0042
  have p0044 := @gSnex A
  have p0045 :=
    @gPm32i
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      (.classMem (synCsn A) (synCvv)) p0043 p0044
  have p0046 :=
    @gFvco2 (synCvv) (synCsn A) (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
  have p0047 := Nominal.mp p0045 p0046
  have p0085 :=
    @gFvtxpvv (synCsn A)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn) p0008 p0037 p0044
  have p0092 :=
    @gFvconst2 (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCsn A) p0006
  have p0093 := Nominal.mp p0044 p0092
  have p0094 := @gWpphwcnsetfnvalndv A hyp_wpphwgendomfnvalndv_1
  have p0095 :=
    @gOpeq12i
      (synCfv (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCsn A))
      (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCfv (synCwpphwcnsetfn) (synCsn A)) (synChwcn A) p0093 p0094
  have p0096 :=
    @gEqtri
      (synCfv (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCsn A))
      (synCop (synCfv (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCsn A))
        (synCfv (synCwpphwcnsetfn) (synCsn A)))
      (synCop (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
      p0085 p0095
  have p0097 :=
    @gFveq2i
      (synCfv (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCsn A))
      (synCop (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
      (synClnimageresfn) p0096
  have p0098 :=
    @gEqtri
      (synCfv (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCsn A))
      (synCfv (synClnimageresfn) (synCfv (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn)) (synCsn A)))
      (synCfv (synClnimageresfn)
        (synCop (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      p0047 p0097
  have p0104 := @gHwcnex A hyp_wpphwgendomfnvalndv_1
  have p0105 :=
    @gLnimageresfnval (synChwcn A)
      (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) p0006 p0104
  have p0106 :=
    @gEqtri
      (synCfv (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCsn A))
      (synCfv (synClnimageresfn)
        (synCop (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
      p0098 p0105
  have p0107 :=
    @gEqtri (synCfv (synCwpphwgendomfn) (synCsn A))
      (synCfv (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCsn A))
      (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
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

/-- Checked nominal proof certificate identified upstream as `g_wpphwgencnvfnvalndv`. -/
@[expose]
noncomputable def gWpphwgencnvfnvalndv (A : Class)
    (hyp_wpphwgencnvfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpphwgencnvfn) (synCsn A)) (synCcnv
          (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphwgencnvfn))
  have p0001 :=
    @gFveq1i (synCsn A) (synCwpphwgencnvfn)
      (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) p0000
  have p0002 := @gLnimageresfnfn
  have p0003 := @gHwgenex
  have p0004 := @gHwbijex
  have p0005 := @gVvex
  have p0006 := @gXpex (synChwbij) (synCvv) p0004 p0005
  have p0007 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0003 p0006
  have p0008 :=
    @gFnconstg (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCvv)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gImageswapfn
  have p0012 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0013 := @gHwcodesunivndv
  have p0014 := @gWeex
  have p0015 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0013 p0014
  have p0016 := @gHwrelsex
  have p0017 := @gInex (synChwcodes (synCvv)) (synChwrels) p0015 p0016
  have p0018 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0012 p0017
  have p0019 := @gCnvex (synChwcn (synCvv)) p0018
  have p0020 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gSsetex
  have p0023 := @gCnvex (synCsset) p0022
  have p0024 := @gWppimagefn (synCcnv (synCsset)) p0023
  have p0025 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0026 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0025
  have p0027 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0024 p0026
  have p0028 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0021 p0027
  have p0029 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0030 := Nominal.mp p0028 p0029
  have p0031 := @gInidm (synCvv)
  have p0032 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0031
  have p0033 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0030 p0032
  have p0034 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0002 p0033
  have p0035 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0010 p0034
  have p0036 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0037 :=
    @gFneq1i (synCvv) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0036
  have p0038 :=
    @gMpbir (synWfn (synCwpphwcnsetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCvv))
      p0035 p0037
  have p0039 :=
    @gPm32i
      (synWfn (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0009 p0038
  have p0040 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)
  have p0041 := Nominal.mp p0039 p0040
  have p0043 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0031
  have p0044 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      p0041 p0043
  have p0045 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0002 p0044
  have p0046 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0047 :=
    @gFneq1i (synCvv) (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      p0046
  have p0048 :=
    @gMpbir (synWfn (synCwpphwgendomfn) (synCvv))
      (synWfn (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCvv))
      p0045 p0047
  have p0049 := @gSnex A
  have p0050 :=
    @gPm32i (synWfn (synCwpphwgendomfn) (synCvv)) (.classMem (synCsn A) (synCvv))
      p0048 p0049
  have p0051 :=
    @gFvco2 (synCvv) (synCsn A) (synCimage (synCswap)) (synCwpphwgendomfn)
  have p0052 := Nominal.mp p0050 p0051
  have p0053 := @gWpphwgendomfnvalndv A hyp_wpphwgencnvfnvalndv_1
  have p0054 :=
    @gFveq2i (synCfv (synCwpphwgendomfn) (synCsn A))
      (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
      (synCimage (synCswap)) p0053
  have p0055 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCsn A))
      (synCfv (synCimage (synCswap)) (synCfv (synCwpphwgendomfn) (synCsn A)))
      (synCfv (synCimage (synCswap))
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      p0052 p0054
  have p0061 := @gHwcnex A hyp_wpphwgencnvfnvalndv_1
  have p0062 :=
    @gResex (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A) p0007
      p0061
  have p0063 :=
    @gWppimageswapfv
      (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
      p0062
  have p0064 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCsn A))
      (synCfv (synCimage (synCswap))
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      (synCcnv
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      p0055 p0063
  have p0065 :=
    @gEqtri (synCfv (synCwpphwgencnvfn) (synCsn A))
      (synCfv (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCsn A))
      (synCcnv
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      p0001 p0064
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_wpphwnisosetfnvalndv`. -/
@[expose]
noncomputable def gWpphwnisosetfnvalndv (A : Class)
    (hyp_wpphwnisosetfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCfv (synCwpphwnisosetfn) (synCsn A)) (synChwniso A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphwnisosetfn))
  have p0001 :=
    @gFveq1i (synCsn A) (synCwpphwnisosetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))))
      p0000
  have p0002 := @gLnimageresfnfn
  have p0003 := @gImageswapfn
  have p0005 := @gHwgenex
  have p0006 := @gHwbijex
  have p0007 := @gVvex
  have p0008 := @gXpex (synChwbij) (synCvv) p0006 p0007
  have p0009 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0005 p0008
  have p0010 :=
    @gFnconstg (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCvv)
  have p0011 := Nominal.mp p0009 p0010
  have p0014 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0015 := @gHwcodesunivndv
  have p0016 := @gWeex
  have p0017 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0015 p0016
  have p0018 := @gHwrelsex
  have p0019 := @gInex (synChwcodes (synCvv)) (synChwrels) p0017 p0018
  have p0020 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0014 p0019
  have p0021 := @gCnvex (synChwcn (synCvv)) p0020
  have p0022 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := @gSsetex
  have p0025 := @gCnvex (synCsset) p0024
  have p0026 := @gWppimagefn (synCcnv (synCsset)) p0025
  have p0027 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0028 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0027
  have p0029 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0026 p0028
  have p0030 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0023 p0029
  have p0031 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := @gInidm (synCvv)
  have p0034 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0033
  have p0035 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0032 p0034
  have p0036 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0002 p0035
  have p0037 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0003 p0036
  have p0038 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0039 :=
    @gFneq1i (synCvv) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0038
  have p0040 :=
    @gMpbir (synWfn (synCwpphwcnsetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCvv))
      p0037 p0039
  have p0041 :=
    @gPm32i
      (synWfn (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0011 p0040
  have p0042 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)
  have p0043 := Nominal.mp p0041 p0042
  have p0045 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0033
  have p0046 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      p0043 p0045
  have p0047 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0002 p0046
  have p0048 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0049 :=
    @gFneq1i (synCvv) (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      p0048
  have p0050 :=
    @gMpbir (synWfn (synCwpphwgendomfn) (synCvv))
      (synWfn (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCvv))
      p0047 p0049
  have p0051 := @gFncovv (synCimage (synCswap)) (synCwpphwgendomfn) p0003 p0050
  have p0052 := (Nominal.classEqRefl (synCwpphwgencnvfn))
  have p0053 :=
    @gFneq1i (synCvv) (synCwpphwgencnvfn)
      (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) p0052
  have p0054 :=
    @gMpbir (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCvv)) p0051
      p0053
  have p0084 :=
    @gPm32i (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0054 p0040
  have p0085 := @gFntxp (synCvv) (synCvv) (synCwpphwgencnvfn) (synCwpphwcnsetfn)
  have p0086 := Nominal.mp p0084 p0085
  have p0088 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) p0033
  have p0089 :=
    @gMpbi
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCvv)) p0086 p0088
  have p0090 :=
    @gFncovv (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
      p0002 p0089
  have p0091 := @gSnex A
  have p0092 :=
    @gPm32i
      (synWfn
        (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
        (synCvv))
      (.classMem (synCsn A) (synCvv)) p0090 p0091
  have p0093 :=
    @gFvco2 (synCvv) (synCsn A) (synCimage (synCswap))
      (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
  have p0094 := Nominal.mp p0092 p0093
  have p0183 :=
    @gPm32i (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCvv))
      (.classMem (synCsn A) (synCvv)) p0089 p0091
  have p0184 :=
    @gFvco2 (synCvv) (synCsn A) (synClnimageresfn)
      (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
  have p0185 := Nominal.mp p0183 p0184
  have p0268 :=
    @gFvtxpvv (synCsn A) (synCwpphwgencnvfn) (synCwpphwcnsetfn) p0054 p0040 p0091
  have p0269 := @gWpphwgencnvfnvalndv A hyp_wpphwnisosetfnvalndv_1
  have p0270 := @gWpphwcnsetfnvalndv A hyp_wpphwnisosetfnvalndv_1
  have p0271 :=
    @gOpeq12i (synCfv (synCwpphwgencnvfn) (synCsn A))
      (synCcnv
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      (synCfv (synCwpphwcnsetfn) (synCsn A)) (synChwcn A) p0269 p0270
  have p0272 :=
    @gEqtri (synCfv (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCsn A))
      (synCop (synCfv (synCwpphwgencnvfn) (synCsn A))
        (synCfv (synCwpphwcnsetfn) (synCsn A)))
      (synCop (synCcnv (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
            (synChwcn A))) (synChwcn A))
      p0268 p0271
  have p0273 :=
    @gFveq2i (synCfv (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCsn A))
      (synCop (synCcnv (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
            (synChwcn A))) (synChwcn A))
      (synClnimageresfn) p0272
  have p0274 :=
    @gEqtri
      (synCfv
        (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
        (synCsn A))
      (synCfv (synClnimageresfn)
        (synCfv (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCsn A)))
      (synCfv (synClnimageresfn) (synCop (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      p0185 p0273
  have p0280 := @gHwcnex A hyp_wpphwnisosetfnvalndv_1
  have p0281 :=
    @gResex (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A) p0009
      p0280
  have p0282 :=
    @gCnvex
      (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A))
      p0281
  have p0284 :=
    @gLnimageresfnval (synChwcn A)
      (synCcnv
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      p0282 p0280
  have p0285 :=
    @gEqtri
      (synCfv
        (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
        (synCsn A))
      (synCfv (synClnimageresfn) (synCop (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      (synCres (synCcnv (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
            (synChwcn A))) (synChwcn A))
      p0274 p0284
  have p0286 :=
    @gFveq2i
      (synCfv
        (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
        (synCsn A))
      (synCres (synCcnv (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
            (synChwcn A))) (synChwcn A))
      (synCimage (synCswap)) p0285
  have p0287 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCsn A))
      (synCfv (synCimage (synCswap)) (synCfv (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))) (synCsn A)))
      (synCfv (synCimage (synCswap)) (synCres (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      p0094 p0286
  have p0297 :=
    @gResex
      (synCcnv
        (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
      (synChwcn A) p0282 p0280
  have p0298 :=
    @gWppimageswapfv
      (synCres (synCcnv (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
            (synChwcn A))) (synChwcn A))
      p0297
  have p0299 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCsn A))
      (synCfv (synCimage (synCswap)) (synCres (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      (synCcnv (synCres (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      p0287 p0298
  have p0300 := @gHwnisogendrrndv A
  have p0301 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCsn A))
      (synCcnv (synCres (synCcnv
            (synCres (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synChwcn A)))
          (synChwcn A)))
      (synChwniso A) p0299 p0300
  have p0302 :=
    @gEqtri (synCfv (synCwpphwnisosetfn) (synCsn A))
      (synCfv (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCsn A))
      (synChwniso A) p0001 p0301
  exact p0302

/-- Checked nominal proof certificate identified upstream as `g_wpphnpairfnvalndv`. -/
@[expose]
noncomputable def gWpphnpairfnvalndv (A : Class)
    (hyp_wpphnpairfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpphnpairfn) (synCsn A))
        (synCop (synChwniso A) (synChwcn A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphnpairfn))
  have p0001 :=
    @gFveq1i (synCsn A) (synCwpphnpairfn)
      (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) p0000
  have p0002 := @gImageswapfn
  have p0003 := @gLnimageresfnfn
  have p0006 := @gHwgenex
  have p0007 := @gHwbijex
  have p0008 := @gVvex
  have p0009 := @gXpex (synChwbij) (synCvv) p0007 p0008
  have p0010 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0006 p0009
  have p0011 :=
    @gFnconstg (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0015 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0016 := @gHwcodesunivndv
  have p0017 := @gWeex
  have p0018 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0016 p0017
  have p0019 := @gHwrelsex
  have p0020 := @gInex (synChwcodes (synCvv)) (synChwrels) p0018 p0019
  have p0021 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0015 p0020
  have p0022 := @gCnvex (synChwcn (synCvv)) p0021
  have p0023 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 := @gSsetex
  have p0026 := @gCnvex (synCsset) p0025
  have p0027 := @gWppimagefn (synCcnv (synCsset)) p0026
  have p0028 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0029 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0028
  have p0030 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0027 p0029
  have p0031 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0024 p0030
  have p0032 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0033 := Nominal.mp p0031 p0032
  have p0034 := @gInidm (synCvv)
  have p0035 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0034
  have p0036 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0033 p0035
  have p0037 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0003 p0036
  have p0038 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0002 p0037
  have p0039 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0040 :=
    @gFneq1i (synCvv) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0039
  have p0041 :=
    @gMpbir (synWfn (synCwpphwcnsetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCvv))
      p0038 p0040
  have p0042 :=
    @gPm32i
      (synWfn (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0012 p0041
  have p0043 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)
  have p0044 := Nominal.mp p0042 p0043
  have p0046 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0034
  have p0047 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      p0044 p0046
  have p0048 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0003 p0047
  have p0049 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0050 :=
    @gFneq1i (synCvv) (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      p0049
  have p0051 :=
    @gMpbir (synWfn (synCwpphwgendomfn) (synCvv))
      (synWfn (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCvv))
      p0048 p0050
  have p0052 := @gFncovv (synCimage (synCswap)) (synCwpphwgendomfn) p0002 p0051
  have p0053 := (Nominal.classEqRefl (synCwpphwgencnvfn))
  have p0054 :=
    @gFneq1i (synCvv) (synCwpphwgencnvfn)
      (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) p0053
  have p0055 :=
    @gMpbir (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCvv)) p0052
      p0054
  have p0085 :=
    @gPm32i (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0055 p0041
  have p0086 := @gFntxp (synCvv) (synCvv) (synCwpphwgencnvfn) (synCwpphwcnsetfn)
  have p0087 := Nominal.mp p0085 p0086
  have p0089 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) p0034
  have p0090 :=
    @gMpbi
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCvv)) p0087 p0089
  have p0091 :=
    @gFncovv (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
      p0003 p0090
  have p0092 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
      p0002 p0091
  have p0093 := (Nominal.classEqRefl (synCwpphwnisosetfn))
  have p0094 :=
    @gFneq1i (synCvv) (synCwpphwnisosetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))))
      p0093
  have p0095 :=
    @gMpbir (synWfn (synCwpphwnisosetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCvv))
      p0092 p0094
  have p0125 := @gSnex A
  have p0126 :=
    @gFvtxpvv (synCsn A) (synCwpphwnisosetfn) (synCwpphwcnsetfn) p0095 p0041 p0125
  have p0127 := @gWpphwnisosetfnvalndv A hyp_wpphnpairfnvalndv_1
  have p0128 := @gWpphwcnsetfnvalndv A hyp_wpphnpairfnvalndv_1
  have p0129 :=
    @gOpeq12i (synCfv (synCwpphwnisosetfn) (synCsn A)) (synChwniso A)
      (synCfv (synCwpphwcnsetfn) (synCsn A)) (synChwcn A) p0127 p0128
  have p0130 :=
    @gEqtri (synCfv (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) (synCsn A))
      (synCop (synCfv (synCwpphwnisosetfn) (synCsn A))
        (synCfv (synCwpphwcnsetfn) (synCsn A)))
      (synCop (synChwniso A) (synChwcn A)) p0126 p0129
  have p0131 :=
    @gEqtri (synCfv (synCwpphnpairfn) (synCsn A))
      (synCfv (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) (synCsn A))
      (synCop (synChwniso A) (synChwcn A)) p0001 p0130
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

/-- Checked nominal proof certificate identified upstream as `g_wpphninputfnexndv`. -/
@[expose]
noncomputable def gWpphninputfnexndv :
    Nominal.NPrf (.classMem (synCwpphninputfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphninputfn))
  have p0001 := (Nominal.classEqRefl (synCwpphnpairfn))
  have p0002 := (Nominal.classEqRefl (synCwpphwnisosetfn))
  have p0003 := @gSwapex
  have p0004 := @gImageex (synCswap) p0003
  have p0005 := @gLnimageresfnex
  have p0006 := (Nominal.classEqRefl (synCwpphwgencnvfn))
  have p0009 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0011 := @gVvex
  have p0012 := @gSnex (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
  have p0013 :=
    @gXpex (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))
      p0011 p0012
  have p0014 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0019 := @gSnex (synCcnv (synChwcn (synCvv)))
  have p0020 := @gXpex (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))) p0011 p0019
  have p0021 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0022 := @gSsetex
  have p0023 := @gCnvex (synCsset) p0022
  have p0024 := @gImageex (synCcnv (synCsset)) p0023
  have p0025 :=
    @gEqeltri (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) (synCvv) p0021
      p0024
  have p0026 :=
    @gTxpex (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
      (synCwpppowsetfn) p0020 p0025
  have p0027 :=
    @gCoex (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0005 p0026
  have p0028 :=
    @gCoex (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0004 p0027
  have p0029 :=
    @gEqeltri (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      (synCvv) p0014 p0028
  have p0030 :=
    @gTxpex
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn) p0013 p0029
  have p0031 :=
    @gCoex (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0005 p0030
  have p0032 :=
    @gEqeltri (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      (synCvv) p0009 p0031
  have p0033 := @gCoex (synCimage (synCswap)) (synCwpphwgendomfn) p0004 p0032
  have p0034 :=
    @gEqeltri (synCwpphwgencnvfn)
      (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCvv) p0006 p0033
  have p0051 := @gTxpex (synCwpphwgencnvfn) (synCwpphwcnsetfn) p0034 p0029
  have p0052 :=
    @gCoex (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) p0005
      p0051
  have p0053 :=
    @gCoex (synCimage (synCswap))
      (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
      p0004 p0052
  have p0054 :=
    @gEqeltri (synCwpphwnisosetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))))
      (synCvv) p0002 p0053
  have p0071 := @gTxpex (synCwpphwnisosetfn) (synCwpphwcnsetfn) p0054 p0029
  have p0072 :=
    @gEqeltri (synCwpphnpairfn) (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn))
      (synCvv) p0001 p0071
  have p0073 := @gSiex (synCwpphnpairfn) p0072
  have p0074 :=
    @gEqeltri (synCwpphninputfn) (synCsi (synCwpphnpairfn)) (synCvv) p0000 p0073
  exact p0074

/-- Checked nominal proof certificate identified upstream as `g_wpphninputfnmapndv`. -/
@[expose]
noncomputable def gWpphninputfnmapndv :
    Nominal.NPrf (synWf (synCwpphninputfn) (synCpw1 (synCvv)) (synCpw1 (synCvv))) :=
  by
  have p0000 := @gImageswapfn
  have p0001 := @gLnimageresfnfn
  have p0004 := @gHwgenex
  have p0005 := @gHwbijex
  have p0006 := @gVvex
  have p0007 := @gXpex (synChwbij) (synCvv) p0005 p0006
  have p0008 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0004 p0007
  have p0009 :=
    @gFnconstg (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCvv)
  have p0010 := Nominal.mp p0008 p0009
  have p0013 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0014 := @gHwcodesunivndv
  have p0015 := @gWeex
  have p0016 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0014 p0015
  have p0017 := @gHwrelsex
  have p0018 := @gInex (synChwcodes (synCvv)) (synChwrels) p0016 p0017
  have p0019 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0013 p0018
  have p0020 := @gCnvex (synChwcn (synCvv)) p0019
  have p0021 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0022 := Nominal.mp p0020 p0021
  have p0023 := @gSsetex
  have p0024 := @gCnvex (synCsset) p0023
  have p0025 := @gWppimagefn (synCcnv (synCsset)) p0024
  have p0026 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0027 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0026
  have p0028 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0025 p0027
  have p0029 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0022 p0028
  have p0030 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0031 := Nominal.mp p0029 p0030
  have p0032 := @gInidm (synCvv)
  have p0033 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0032
  have p0034 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0031 p0033
  have p0035 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0001 p0034
  have p0036 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0000 p0035
  have p0037 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0038 :=
    @gFneq1i (synCvv) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0037
  have p0039 :=
    @gMpbir (synWfn (synCwpphwcnsetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCvv))
      p0036 p0038
  have p0040 :=
    @gPm32i
      (synWfn (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0010 p0039
  have p0041 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)
  have p0042 := Nominal.mp p0040 p0041
  have p0044 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0032
  have p0045 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      p0042 p0044
  have p0046 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0001 p0045
  have p0047 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0048 :=
    @gFneq1i (synCvv) (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      p0047
  have p0049 :=
    @gMpbir (synWfn (synCwpphwgendomfn) (synCvv))
      (synWfn (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCvv))
      p0046 p0048
  have p0050 := @gFncovv (synCimage (synCswap)) (synCwpphwgendomfn) p0000 p0049
  have p0051 := (Nominal.classEqRefl (synCwpphwgencnvfn))
  have p0052 :=
    @gFneq1i (synCvv) (synCwpphwgencnvfn)
      (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) p0051
  have p0053 :=
    @gMpbir (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCvv)) p0050
      p0052
  have p0083 :=
    @gPm32i (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0053 p0039
  have p0084 := @gFntxp (synCvv) (synCvv) (synCwpphwgencnvfn) (synCwpphwcnsetfn)
  have p0085 := Nominal.mp p0083 p0084
  have p0087 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) p0032
  have p0088 :=
    @gMpbi
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCvv)) p0085 p0087
  have p0089 :=
    @gFncovv (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
      p0001 p0088
  have p0090 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
      p0000 p0089
  have p0091 := (Nominal.classEqRefl (synCwpphwnisosetfn))
  have p0092 :=
    @gFneq1i (synCvv) (synCwpphwnisosetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))))
      p0091
  have p0093 :=
    @gMpbir (synWfn (synCwpphwnisosetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCvv))
      p0090 p0092
  have p0123 :=
    @gPm32i (synWfn (synCwpphwnisosetfn) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0093 p0039
  have p0124 := @gFntxp (synCvv) (synCvv) (synCwpphwnisosetfn) (synCwpphwcnsetfn)
  have p0125 := Nominal.mp p0123 p0124
  have p0127 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) p0032
  have p0128 :=
    @gMpbi
      (synWfn (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) (synCvv)) p0125 p0127
  have p0129 := (Nominal.classEqRefl (synCwpphnpairfn))
  have p0130 :=
    @gFneq1i (synCvv) (synCwpphnpairfn)
      (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) p0129
  have p0131 :=
    @gMpbir (synWfn (synCwpphnpairfn) (synCvv))
      (synWfn (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) (synCvv)) p0128 p0130
  have p0132 := @gSsv (synCrn (synCwpphnpairfn))
  have p0133 :=
    @gPm32i (synWfn (synCwpphnpairfn) (synCvv))
      (synWss (synCrn (synCwpphnpairfn)) (synCvv)) p0131 p0132
  have p0134 := (Nominal.biimpRefl (synWf (synCwpphnpairfn) (synCvv) (synCvv)))
  have p0135 :=
    @gMpbir (synWf (synCwpphnpairfn) (synCvv) (synCvv))
      (synWa (synWfn (synCwpphnpairfn) (synCvv))
        (synWss (synCrn (synCwpphnpairfn)) (synCvv)))
      p0133 p0134
  have p0136 := @gSifmap (synCvv) (synCvv) (synCwpphnpairfn)
  have p0137 := Nominal.mp p0135 p0136
  have p0138 := (Nominal.classEqRefl (synCwpphninputfn))
  have p0139 :=
    @gFeq1i (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCwpphninputfn)
      (synCsi (synCwpphnpairfn)) p0138
  have p0140 :=
    @gMpbir (synWf (synCwpphninputfn) (synCpw1 (synCvv)) (synCpw1 (synCvv)))
      (synWf (synCsi (synCwpphnpairfn)) (synCpw1 (synCvv)) (synCpw1 (synCvv)))
      p0137 p0139
  exact p0140

/-- Checked nominal proof certificate identified upstream as `g_wpphninputfnvalndv`. -/
@[expose]
noncomputable def gWpphninputfnvalndv (A : Class)
    (hyp_wpphninputfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpphninputfn) (synCsn (synCsn A)))
        (synCsn (synCop (synChwniso A) (synChwcn A)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphninputfn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn A)) (synCwpphninputfn) (synCsi (synCwpphnpairfn)) p0000
  have p0002 := @gSnex A
  have p0003 := @gImageswapfn
  have p0004 := @gLnimageresfnfn
  have p0007 := @gHwgenex
  have p0008 := @gHwbijex
  have p0009 := @gVvex
  have p0010 := @gXpex (synChwbij) (synCvv) p0008 p0009
  have p0011 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0007 p0010
  have p0012 :=
    @gFnconstg (synCvv) (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0016 := (Nominal.classEqRefl (synChwcn (synCvv)))
  have p0017 := @gHwcodesunivndv
  have p0018 := @gWeex
  have p0019 := @gEqeltri (synChwcodes (synCvv)) (synCwe) (synCvv) p0017 p0018
  have p0020 := @gHwrelsex
  have p0021 := @gInex (synChwcodes (synCvv)) (synChwrels) p0019 p0020
  have p0022 :=
    @gEqeltri (synChwcn (synCvv)) (synCin (synChwcodes (synCvv)) (synChwrels))
      (synCvv) p0016 p0021
  have p0023 := @gCnvex (synChwcn (synCvv)) p0022
  have p0024 := @gFnconstg (synCvv) (synCcnv (synChwcn (synCvv))) (synCvv)
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gSsetex
  have p0027 := @gCnvex (synCsset) p0026
  have p0028 := @gWppimagefn (synCcnv (synCsset)) p0027
  have p0029 := (Nominal.classEqRefl (synCwpppowsetfn))
  have p0030 :=
    @gFneq1i (synCvv) (synCwpppowsetfn) (synCimage (synCcnv (synCsset))) p0029
  have p0031 :=
    @gMpbir (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCimage (synCcnv (synCsset))) (synCvv)) p0028 p0030
  have p0032 :=
    @gPm32i
      (synWfn (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCvv))
      (synWfn (synCwpppowsetfn) (synCvv)) p0025 p0031
  have p0033 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv))))) (synCwpppowsetfn)
  have p0034 := Nominal.mp p0032 p0033
  have p0035 := @gInidm (synCvv)
  have p0036 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0035
  have p0037 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)) (synCvv))
      p0034 p0036
  have p0038 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
        (synCwpppowsetfn))
      p0004 p0037
  have p0039 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn)
        (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
          (synCwpppowsetfn)))
      p0003 p0038
  have p0040 := (Nominal.classEqRefl (synCwpphwcnsetfn))
  have p0041 :=
    @gFneq1i (synCvv) (synCwpphwcnsetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
            (synCwpppowsetfn))))
      p0040
  have p0042 :=
    @gMpbir (synWfn (synCwpphwcnsetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCxp (synCvv) (synCsn (synCcnv (synChwcn (synCvv)))))
              (synCwpppowsetfn)))) (synCvv))
      p0039 p0041
  have p0043 :=
    @gPm32i
      (synWfn (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv))))) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0013 p0042
  have p0044 :=
    @gFntxp (synCvv) (synCvv)
      (synCxp (synCvv) (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
      (synCwpphwcnsetfn)
  have p0045 := Nominal.mp p0043 p0044
  have p0047 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0035
  have p0048 :=
    @gMpbi
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)) (synCvv))
      p0045 p0047
  have p0049 :=
    @gFncovv (synClnimageresfn)
      (synCtxp (synCxp (synCvv)
          (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
        (synCwpphwcnsetfn))
      p0004 p0048
  have p0050 := (Nominal.classEqRefl (synCwpphwgendomfn))
  have p0051 :=
    @gFneq1i (synCvv) (synCwpphwgendomfn)
      (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
            (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
          (synCwpphwcnsetfn)))
      p0050
  have p0052 :=
    @gMpbir (synWfn (synCwpphwgendomfn) (synCvv))
      (synWfn (synCcom (synClnimageresfn) (synCtxp (synCxp (synCvv)
              (synCsn (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))))
            (synCwpphwcnsetfn))) (synCvv))
      p0049 p0051
  have p0053 := @gFncovv (synCimage (synCswap)) (synCwpphwgendomfn) p0003 p0052
  have p0054 := (Nominal.classEqRefl (synCwpphwgencnvfn))
  have p0055 :=
    @gFneq1i (synCvv) (synCwpphwgencnvfn)
      (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) p0054
  have p0056 :=
    @gMpbir (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCwpphwgendomfn)) (synCvv)) p0053
      p0055
  have p0086 :=
    @gPm32i (synWfn (synCwpphwgencnvfn) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0056 p0042
  have p0087 := @gFntxp (synCvv) (synCvv) (synCwpphwgencnvfn) (synCwpphwcnsetfn)
  have p0088 := Nominal.mp p0086 p0087
  have p0090 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) p0035
  have p0091 :=
    @gMpbi
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)) (synCvv)) p0088 p0090
  have p0092 :=
    @gFncovv (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))
      p0004 p0091
  have p0093 :=
    @gFncovv (synCimage (synCswap))
      (synCcom (synClnimageresfn) (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))
      p0003 p0092
  have p0094 := (Nominal.classEqRefl (synCwpphwnisosetfn))
  have p0095 :=
    @gFneq1i (synCvv) (synCwpphwnisosetfn)
      (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
          (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn))))
      p0094
  have p0096 :=
    @gMpbir (synWfn (synCwpphwnisosetfn) (synCvv))
      (synWfn (synCcom (synCimage (synCswap)) (synCcom (synClnimageresfn)
            (synCtxp (synCwpphwgencnvfn) (synCwpphwcnsetfn)))) (synCvv))
      p0093 p0095
  have p0126 :=
    @gPm32i (synWfn (synCwpphwnisosetfn) (synCvv))
      (synWfn (synCwpphwcnsetfn) (synCvv)) p0096 p0042
  have p0127 := @gFntxp (synCvv) (synCvv) (synCwpphwnisosetfn) (synCwpphwcnsetfn)
  have p0128 := Nominal.mp p0126 p0127
  have p0130 :=
    @gFneq2i (synCin (synCvv) (synCvv)) (synCvv)
      (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) p0035
  have p0131 :=
    @gMpbi
      (synWfn (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn))
        (synCin (synCvv) (synCvv)))
      (synWfn (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) (synCvv)) p0128 p0130
  have p0132 := (Nominal.classEqRefl (synCwpphnpairfn))
  have p0133 :=
    @gFneq1i (synCvv) (synCwpphnpairfn)
      (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) p0132
  have p0134 :=
    @gMpbir (synWfn (synCwpphnpairfn) (synCvv))
      (synWfn (synCtxp (synCwpphwnisosetfn) (synCwpphwcnsetfn)) (synCvv)) p0131 p0133
  have p0135 := @gSsv (synCrn (synCwpphnpairfn))
  have p0136 :=
    @gPm32i (synWfn (synCwpphnpairfn) (synCvv))
      (synWss (synCrn (synCwpphnpairfn)) (synCvv)) p0134 p0135
  have p0137 := (Nominal.biimpRefl (synWf (synCwpphnpairfn) (synCvv) (synCvv)))
  have p0138 :=
    @gMpbir (synWf (synCwpphnpairfn) (synCvv) (synCvv))
      (synWa (synWfn (synCwpphnpairfn) (synCvv))
        (synWss (synCrn (synCwpphnpairfn)) (synCvv)))
      p0136 p0137
  have p0139 := @gSifvald (synCvv) (synCvv) (synCsn A) (synCwpphnpairfn) p0138
  have p0140 := Nominal.mp p0002 p0139
  have p0141 := @gWpphnpairfnvalndv A hyp_wpphninputfnvalndv_1
  have p0142 :=
    @gSneqi (synCfv (synCwpphnpairfn) (synCsn A))
      (synCop (synChwniso A) (synChwcn A)) p0141
  have p0143 :=
    @gEqtri (synCfv (synCsi (synCwpphnpairfn)) (synCsn (synCsn A)))
      (synCsn (synCfv (synCwpphnpairfn) (synCsn A)))
      (synCsn (synCop (synChwniso A) (synChwcn A))) p0140 p0142
  have p0144 :=
    @gEqtri (synCfv (synCwpphninputfn) (synCsn (synCsn A)))
      (synCfv (synCsi (synCwpphnpairfn)) (synCsn (synCsn A)))
      (synCsn (synCop (synChwniso A) (synChwcn A))) p0001 p0143
  exact p0144

/-- Checked nominal proof certificate identified upstream as `g_fdpointimagevvdndv`. -/
@[expose]
noncomputable def gFdpointimagevvdndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv))
        (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn A)))
          (synCpw1 (synCpw1 A)))) :=
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
  have dv_cache_0001 : c ∉ ((synCvv)).fv := by
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
      ((Wff.imp (.classMem A (synCvv))
          (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn A)))
            (synCpw1 (synCpw1 A))))).fv :=
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
  have p0000 := @gId (.classMem A (synCvv))
  have p0001 := @gId (.classEq (.cv c) A)
  have p0002 := @gEleq1d (.classEq (.cv c) A) (.cv c) A (synCvv) p0001
  have p0004 := @gSneqd (.classEq (.cv c) A) (.cv c) A p0001
  have p0005 := @gSneqd (.classEq (.cv c) A) (synCsn (.cv c)) (synCsn A) p0004
  have p0006 :=
    @gImaeq2d (.classEq (.cv c) A) (synCsn (synCsn (.cv c))) (synCsn (synCsn A))
      (synCfdpointrel (synCvv)) p0005
  have p0008 := @gPw1eq (.cv c) A
  have p0009 :=
    @gSyl (.classEq (.cv c) A) (.classEq (.cv c) A)
      (.classEq (synCpw1 (.cv c)) (synCpw1 A)) p0001 p0008
  have p0010 := @gPw1eq (synCpw1 (.cv c)) (synCpw1 A)
  have p0011 :=
    @gSyl (.classEq (.cv c) A) (.classEq (synCpw1 (.cv c)) (synCpw1 A))
      (.classEq (synCpw1 (synCpw1 (.cv c))) (synCpw1 (synCpw1 A))) p0009 p0010
  have p0012 :=
    @gEqeq12d (.classEq (.cv c) A)
      (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn (.cv c))))
      (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn A)))
      (synCpw1 (synCpw1 (.cv c))) (synCpw1 (synCpw1 A)) p0006 p0011
  have p0013 :=
    @gImbi12d (.classEq (.cv c) A) (.classMem (.cv c) (synCvv)) (.classMem A (synCvv))
      (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn (.cv c))))
        (synCpw1 (synCpw1 (.cv c))))
      (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn A)))
        (synCpw1 (synCpw1 A)))
      p0002 p0012
  have p0014 := @gVvex
  have p0015 := @gFdpointimage (synCvv) c dv_cache_0001 p0014
  have p0016 :=
    @gVtoclg
      (.imp (.classMem (.cv c) (synCvv))
        (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn (.cv c))))
          (synCpw1 (synCpw1 (.cv c)))))
      (.imp (.classMem A (synCvv))
        (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn A)))
          (synCpw1 (synCpw1 A))))
      c A (synCvv) dv_cache_0002 dv_cache_0003 p0013 p0015
  have p0017 :=
    @gMpd (.classMem A (synCvv)) (.classMem A (synCvv))
      (.classEq (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn A)))
        (synCpw1 (synCpw1 A)))
      p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelkernelexndv`. -/
@[expose]
noncomputable def gWppqkrelkernelexndv :
    Nominal.NPrf (.classMem (synCwppqkrelkernel) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppqkrelkernel))
  have p0001 := @gVvex
  have p0004 := @gXpkex (synCvv) (synCvv) p0001 p0001
  have p0005 := @gXpkex (synCvv) (synCxpk (synCvv) (synCvv)) p0001 p0004
  have p0006 := @gSetconslem5
  have p0007 :=
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
      p0005 p0006
  have p0008 :=
    @gEqeltri (synCwppqkrelkernel)
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
      (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wppqkrelkernelvalndv`. -/
@[expose]
noncomputable def gWppqkrelkernelvalndv (A : Class) :
    Nominal.NPrf
      (.classEq (synCimak (synCwppqkrelkernel) (synCpw1 (synCpw1 A))) (synCqkrel A)) :=
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
  have p0000 := (Nominal.classEqRefl (synCwppqkrelkernel))
  have p0001 :=
    @gImakeq1i (synCwppqkrelkernel)
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
      (synCpw1 (synCpw1 A)) p0000
  have p0002 :=
    @gSetconslem6 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQkrel x y z A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0004 :=
    @gEqtr4i
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
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.classMem (synCop (.cv x) (.cv y)) A)))))
      (synCqkrel A) p0002 p0003
  have p0005 :=
    @gEqtri (synCimak (synCwppqkrelkernel) (synCpw1 (synCpw1 A)))
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
      (synCqkrel A) p0001 p0004
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

/-- Checked nominal proof certificate identified upstream as `g_hwnisolnkereqndv`. -/
@[expose]
noncomputable def gHwnisolnkereqndv (A : Class)
    (hyp_hwnisolnkereqndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synClnker (synChwniso A)) (synChwniso A)) :=
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
  have dv_cache_0001 : x ∉ ((synClnker (synChwniso A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synClnker (synChwniso A))).fv :=
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
  have dv_cache_0003 : x ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0004 : y ∉ ((synChwniso A)).fv :=
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
  have p0000 := @gBrlnker (synChwniso A) (.cv x) (.cv y)
  have p0001 :=
    @gSimpl (synWbr (.cv x) (synChwniso A) (.cv y))
      (synWbr (.cv y) (synChwniso A) (.cv x))
  have p0002 := @gId (synWbr (.cv x) (synChwniso A) (.cv y))
  have p0003 := @gHwnisoerv A
  have p0004 := Nominal.mp hyp_hwnisolnkereqndv_1 p0003
  have p0005 :=
    @gA1i (synWbr (synChwniso A) (synCer) (synCvv))
      (synWbr (.cv x) (synChwniso A) (.cv y)) p0004
  have p0006 := @gBrreldmex (.cv x) (.cv y) (synChwniso A)
  have p0007 := @gBrrelrnex (.cv x) (.cv y) (synChwniso A)
  have p0009 :=
    @gErsym (synWbr (.cv x) (synChwniso A) (.cv y)) (synCvv) (synChwniso A) (.cv x)
      (.cv y) p0005 p0006 p0007 p0002
  have p0010 :=
    @gJca (synWbr (.cv x) (synChwniso A) (.cv y))
      (synWbr (.cv x) (synChwniso A) (.cv y)) (synWbr (.cv y) (synChwniso A) (.cv x))
      p0002 p0009
  have p0011 :=
    @gImpbii
      (synWa (synWbr (.cv x) (synChwniso A) (.cv y))
        (synWbr (.cv y) (synChwniso A) (.cv x)))
      (synWbr (.cv x) (synChwniso A) (.cv y)) p0001 p0010
  have p0012 :=
    @gBitri (synWbr (.cv x) (synClnker (synChwniso A)) (.cv y))
      (synWa (synWbr (.cv x) (synChwniso A) (.cv y))
        (synWbr (.cv y) (synChwniso A) (.cv x)))
      (synWbr (.cv x) (synChwniso A) (.cv y)) p0000 p0011
  have p0013 :=
    @gEqbrriv x y (synClnker (synChwniso A)) (synChwniso A) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_lnpwhnordvalndv`. -/
@[expose]
noncomputable def gLnpwhnordvalndv (A : Class)
    (hyp_lnpwhnordvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synClnpwquofn) (synCsn (synCop (synChwniso A) (synChwcn A))))
        (synChnord A)) :=
  by
  have p0000 := @gHwnisoex A hyp_lnpwhnordvalndv_1
  have p0001 := @gHwcnex A hyp_lnpwhnordvalndv_1
  have p0002 := @gLnpwquofnval (synChwcn A) (synChwniso A) p0000 p0001
  have p0003 := @gHwnisolnkereqndv A hyp_lnpwhnordvalndv_1
  have p0004 := @gQseq2 (synClnker (synChwniso A)) (synChwniso A) (synChwcn A)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := (Nominal.classEqRefl (synChnord A))
  have p0007 := @gEqcomi (synChnord A) (synCqs (synChwcn A) (synChwniso A)) p0006
  have p0008 :=
    @gEqtri (synCqs (synChwcn A) (synClnker (synChwniso A)))
      (synCqs (synChwcn A) (synChwniso A)) (synChnord A) p0005 p0007
  have p0009 :=
    @gEqtri (synCfv (synClnpwquofn) (synCsn (synCop (synChwniso A) (synChwcn A))))
      (synCqs (synChwcn A) (synClnker (synChwniso A))) (synChnord A) p0002 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordpointfnexndv`. -/
@[expose]
noncomputable def gWpplitphnordpointfnexndv :
    Nominal.NPrf (.classMem (synCwpplitphnordpointfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpplitphnordpointfn))
  have p0001 := @gLnpwquofnex
  have p0002 := @gWpphninputfnexndv
  have p0003 := @gCoex (synClnpwquofn) (synCwpphninputfn) p0001 p0002
  have p0004 :=
    @gEqeltri (synCwpplitphnordpointfn) (synCcom (synClnpwquofn) (synCwpphninputfn))
      (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordpointfnfnndv`. -/
@[expose]
noncomputable def gWpplitphnordpointfnfnndv :
    Nominal.NPrf (synWfn (synCwpplitphnordpointfn) (synCpw1 (synCvv))) :=
  by
  have p0000 := @gLnpwquofnfn
  have p0001 := @gWpphninputfnmapndv
  have p0002 := @gFfn (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCwpphninputfn)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gDffn2 (synCpw1 (synCvv)) (synCwpphninputfn)
  have p0005 :=
    @gMpbi (synWfn (synCwpphninputfn) (synCpw1 (synCvv)))
      (synWf (synCwpphninputfn) (synCpw1 (synCvv)) (synCvv)) p0003 p0004
  have p0006 :=
    @gPm32i (synWfn (synClnpwquofn) (synCvv))
      (synWf (synCwpphninputfn) (synCpw1 (synCvv)) (synCvv)) p0000 p0005
  have p0007 :=
    @gFnfco (synCvv) (synCpw1 (synCvv)) (synClnpwquofn) (synCwpphninputfn)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (synCwpplitphnordpointfn))
  have p0010 :=
    @gFneq1i (synCpw1 (synCvv)) (synCwpplitphnordpointfn)
      (synCcom (synClnpwquofn) (synCwpphninputfn)) p0009
  have p0011 :=
    @gMpbir (synWfn (synCwpplitphnordpointfn) (synCpw1 (synCvv)))
      (synWfn (synCcom (synClnpwquofn) (synCwpphninputfn)) (synCpw1 (synCvv))) p0008
      p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordpointfnvalndv`. -/
@[expose]
noncomputable def gWpplitphnordpointfnvalndv (A : Class)
    (hyp_wpplitphnordpointfnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpplitphnordpointfn) (synCsn (synCsn A))) (synChnord A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpplitphnordpointfn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn A)) (synCwpplitphnordpointfn)
      (synCcom (synClnpwquofn) (synCwpphninputfn)) p0000
  have p0002 := @gWpphninputfnmapndv
  have p0003 := @gFfn (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCwpphninputfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gSnex A
  have p0006 := @gSnelpw1 (synCsn A) (synCvv)
  have p0007 :=
    @gMpbir (.classMem (synCsn (synCsn A)) (synCpw1 (synCvv)))
      (.classMem (synCsn A) (synCvv)) p0005 p0006
  have p0008 :=
    @gPm32i (synWfn (synCwpphninputfn) (synCpw1 (synCvv)))
      (.classMem (synCsn (synCsn A)) (synCpw1 (synCvv))) p0004 p0007
  have p0009 :=
    @gFvco2 (synCpw1 (synCvv)) (synCsn (synCsn A)) (synClnpwquofn)
      (synCwpphninputfn)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gWpphninputfnvalndv A hyp_wpplitphnordpointfnvalndv_1
  have p0012 :=
    @gFveq2i (synCfv (synCwpphninputfn) (synCsn (synCsn A)))
      (synCsn (synCop (synChwniso A) (synChwcn A))) (synClnpwquofn) p0011
  have p0013 :=
    @gEqtri
      (synCfv (synCcom (synClnpwquofn) (synCwpphninputfn)) (synCsn (synCsn A)))
      (synCfv (synClnpwquofn) (synCfv (synCwpphninputfn) (synCsn (synCsn A))))
      (synCfv (synClnpwquofn) (synCsn (synCop (synChwniso A) (synChwcn A)))) p0010
      p0012
  have p0014 := @gLnpwhnordvalndv A hyp_wpplitphnordpointfnvalndv_1
  have p0015 :=
    @gEqtri
      (synCfv (synCcom (synClnpwquofn) (synCwpphninputfn)) (synCsn (synCsn A)))
      (synCfv (synClnpwquofn) (synCsn (synCop (synChwniso A) (synChwcn A))))
      (synChnord A) p0013 p0014
  have p0016 :=
    @gEqtri (synCfv (synCwpplitphnordpointfn) (synCsn (synCsn A)))
      (synCfv (synCcom (synClnpwquofn) (synCwpphninputfn)) (synCsn (synCsn A)))
      (synChnord A) p0001 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hncardnceqsetimpndv`. -/
@[expose]
noncomputable def gHncardnceqsetimpndv (D : Class) (E : Class) :
    Nominal.NPrf
      (.imp (.classMem D (synCvv)) (.imp (.classEq (synCnc D) (synCnc E))
          (.classEq (synChncard D) (synChncard E)))) :=
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
  have p0000 := @gEqncg D E (synCvv)
  have p0001 :=
    @gBiimpd (.classMem D (synCvv)) (.classEq (synCnc D) (synCnc E))
      (synWbr D (synCen) E) p0000
  have p0002 := @gBren D E f dv_cache_0001 dv_cache_0002
  have p0003 := @gBiimpi (synWbr D (synCen) E) (synWex f (synWf1o (.cv f) D E)) p0002
  have p0004 :=
    @gSyl6 (.classMem D (synCvv)) (.classEq (synCnc D) (synCnc E))
      (synWbr D (synCen) E) (synWex f (synWf1o (.cv f) D E)) p0001 p0003
  have p0005 := @gVex f
  have p0006 := @gHncardf1oimpndv D E (.cv f) p0005
  have p0007 :=
    @gExlimiv (synWf1o (.cv f) D E) (.classEq (synChncard D) (synChncard E)) f
      dv_cache_0003 p0006
  have p0008 :=
    @gSyl6 (.classMem D (synCvv)) (.classEq (synCnc D) (synCnc E))
      (synWex f (synWf1o (.cv f) D E)) (.classEq (synChncard D) (synChncard E)) p0004
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_hnordncmemimpndv`. -/
@[expose]
noncomputable def gHnordncmemimpndv (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCnc A)) (.classMem (synChnord B) (synCnc (synChnord A)))) :=
  by
  have p0000 := @gElex B (synCnc A)
  have p0001 := @gHnordexg B
  have p0002 :=
    @gSyl (.classMem B (synCnc A)) (.classMem B (synCvv))
      (.classMem (synChnord B) (synCvv)) p0000 p0001
  have p0003 := @gNcidg (synChnord B) (synCvv)
  have p0004 :=
    @gSyl (.classMem B (synCnc A)) (.classMem (synChnord B) (synCvv))
      (.classMem (synChnord B) (synCnc (synChnord B))) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synChncard B))
  have p0006 := @gEqcomi (synChncard B) (synCnc (synChnord B)) p0005
  have p0007 :=
    @gA1i (.classEq (synCnc (synChnord B)) (synChncard B)) (.classMem B (synCnc A))
      p0006
  have p0008 := @gElnc B A
  have p0009 := @gBiimpi (.classMem B (synCnc A)) (synWbr B (synCen) A) p0008
  have p0011 := @gEqncg B A (synCvv)
  have p0012 :=
    @gSyl (.classMem B (synCnc A)) (.classMem B (synCvv))
      (synWb (.classEq (synCnc B) (synCnc A)) (synWbr B (synCen) A)) p0000 p0011
  have p0013 :=
    @gMpbird (.classMem B (synCnc A)) (.classEq (synCnc B) (synCnc A))
      (synWbr B (synCen) A) p0009 p0012
  have p0015 := @gHncardnceqsetimpndv B A
  have p0016 :=
    @gSyl (.classMem B (synCnc A)) (.classMem B (synCvv))
      (.imp (.classEq (synCnc B) (synCnc A)) (.classEq (synChncard B) (synChncard A)))
      p0000 p0015
  have p0017 :=
    @gMpd (.classMem B (synCnc A)) (.classEq (synCnc B) (synCnc A))
      (.classEq (synChncard B) (synChncard A)) p0013 p0016
  have p0018 :=
    @gEqtrd (.classMem B (synCnc A)) (synCnc (synChnord B)) (synChncard B)
      (synChncard A) p0007 p0017
  have p0019 := (Nominal.classEqRefl (synChncard A))
  have p0020 :=
    @gA1i (.classEq (synChncard A) (synCnc (synChnord A))) (.classMem B (synCnc A))
      p0019
  have p0021 :=
    @gEqtrd (.classMem B (synCnc A)) (synCnc (synChnord B)) (synChncard A)
      (synCnc (synChnord A)) p0018 p0020
  have p0022 :=
    @gEleqtrd (.classMem B (synCnc A)) (synChnord B) (synCnc (synChnord B))
      (synCnc (synChnord A)) p0004 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_enimasatndv`. -/
@[expose]
noncomputable def gEnimasatndv (A : Class) (Q : Class)
    (hyp_enimasatndv_1 : Nominal.NPrf (.classMem A Q))
    (hyp_enimasatndv_2 : Nominal.NPrf (synWss Q (synCnc A))) :
    Nominal.NPrf (.classEq (synCima (synCen) Q) (synCnc A)) :=
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
  have dv_cache_0002 : y ∉ ((synCen)).fv :=
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
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) (synCnc A))).fv :=
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
  have dv_cache_0005 : x ∉ ((synCima (synCen) Q)).fv :=
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
  have dv_cache_0006 : x ∉ ((synCnc A)).fv :=
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
  have p0000 := @gElima y (.cv x) (synCen) Q dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gBiimpi (.classMem (.cv x) (synCima (synCen) Q))
      (synWrex y Q (synWbr (.cv y) (synCen) (.cv x))) p0000
  have p0002 := @gSimpr (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x))
  have p0003 := @gEnsymi (.cv y) (.cv x)
  have p0004 :=
    @gSyl (synWa (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x)))
      (synWbr (.cv y) (synCen) (.cv x)) (synWbr (.cv x) (synCen) (.cv y)) p0002 p0003
  have p0005 := @gSimpl (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x))
  have p0006 := @gSseli Q (synCnc A) (.cv y) hyp_enimasatndv_2
  have p0007 :=
    @gSyl (synWa (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x)))
      (.classMem (.cv y) Q) (.classMem (.cv y) (synCnc A)) p0005 p0006
  have p0008 := @gElnc (.cv y) A
  have p0009 :=
    @gSylib (synWa (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x)))
      (.classMem (.cv y) (synCnc A)) (synWbr (.cv y) (synCen) A) p0007 p0008
  have p0010 :=
    @gJca (synWa (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x)))
      (synWbr (.cv x) (synCen) (.cv y)) (synWbr (.cv y) (synCen) A) p0004 p0009
  have p0011 := @gEntr (.cv x) (.cv y) A
  have p0012 :=
    @gSyl (synWa (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x)))
      (synWa (synWbr (.cv x) (synCen) (.cv y)) (synWbr (.cv y) (synCen) A))
      (synWbr (.cv x) (synCen) A) p0010 p0011
  have p0013 := @gElnc (.cv x) A
  have p0014 :=
    @gSylibr (synWa (.classMem (.cv y) Q) (synWbr (.cv y) (synCen) (.cv x)))
      (synWbr (.cv x) (synCen) A) (.classMem (.cv x) (synCnc A)) p0012 p0013
  have p0015 :=
    @gRexlimiva (synWbr (.cv y) (synCen) (.cv x)) (.classMem (.cv x) (synCnc A)) y Q
      dv_cache_0004 p0014
  have p0016 :=
    @gSyl (.classMem (.cv x) (synCima (synCen) Q))
      (synWrex y Q (synWbr (.cv y) (synCen) (.cv x))) (.classMem (.cv x) (synCnc A))
      p0001 p0015
  have p0017 :=
    @gSsriv x (synCima (synCen) Q) (synCnc A) dv_cache_0005 dv_cache_0006 p0016
  have p0018 := (Nominal.classEqRefl (synCnc A))
  have p0019 := (Nominal.classEqRefl (synCec A (synCen)))
  have p0020 :=
    @gEqtri (synCnc A) (synCec A (synCen)) (synCima (synCen) (synCsn A)) p0018
      p0019
  have p0021 := @gSnssi A Q
  have p0022 := Nominal.mp hyp_enimasatndv_1 p0021
  have p0023 := @gImass2 (synCsn A) Q (synCen)
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gEqsstri (synCnc A) (synCima (synCen) (synCsn A)) (synCima (synCen) Q) p0020
      p0024
  have p0026 := @gEqssi (synCima (synCen) Q) (synCnc A) p0017 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordpointfnvalimpndv`. -/
@[expose]
noncomputable def gWpplitphnordpointfnvalimpndv (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv))))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv q))
          (synChnord (synCuni (synCuni (.cv q)))))) :=
  by
  have dv_cache_0001 : q ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gFdcolcodearg (synCvv) q dv_cache_0001
  have p0001 :=
    @gSimpr (.classMem (synCuni (synCuni (.cv q))) (synCvv))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
  have p0002 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) (synCvv))
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0000 p0001
  have p0003 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv)))) (.cv q)
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) (synCwpplitphnordpointfn) p0002
  have p0004 := @gVex q
  have p0005 := @gUniex (.cv q) p0004
  have p0006 := @gUniex (synCuni (.cv q)) p0005
  have p0007 := @gWpplitphnordpointfnvalndv (synCuni (synCuni (.cv q))) p0006
  have p0008 :=
    @gA1i
      (.classEq (synCfv (synCwpplitphnordpointfn)
          (synCsn (synCsn (synCuni (synCuni (.cv q))))))
        (synChnord (synCuni (synCuni (.cv q)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv)))) p0007
  have p0009 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv))))
      (synCfv (synCwpplitphnordpointfn) (.cv q))
      (synCfv (synCwpplitphnordpointfn) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
      (synChnord (synCuni (synCuni (.cv q)))) p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordimexndv`. -/
@[expose]
noncomputable def gWpplitphnordimexndv (Q : Class)
    (hyp_wpplitphnordimexndv_1 : Nominal.NPrf (.classMem Q (synCvv))) :
    Nominal.NPrf
      (.classMem (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))) (synCvv)) :=
  by
  have p0000 := @gWpplitphnordpointfnexndv
  have p0001 := @gPw1ex Q hyp_wpplitphnordimexndv_1
  have p0002 := @gPw1ex (synCpw1 Q) p0001
  have p0003 := @gImaex (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordimcanndv`. -/
@[expose]
noncomputable def gWpplitphnordimcanndv (C : Class) (Q : Class)
    (_hyp_wpplitphnordimcanndv_1 : Nominal.NPrf (.classMem Q (synCvv)))
    (hyp_wpplitphnordimcanndv_2 : Nominal.NPrf (.classMem C Q)) :
    Nominal.NPrf
      (.classMem (synChnord C)
        (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q)))) :=
  by
  have p0000 := @gElexi C Q hyp_wpplitphnordimcanndv_2
  have p0001 := @gWpplitphnordpointfnvalndv C p0000
  have p0002 :=
    @gEqcomi (synCfv (synCwpplitphnordpointfn) (synCsn (synCsn C))) (synChnord C)
      p0001
  have p0003 := @gSnelpw1 C Q
  have p0004 :=
    @gMpbir (.classMem (synCsn C) (synCpw1 Q)) (.classMem C Q)
      hyp_wpplitphnordimcanndv_2 p0003
  have p0005 := @gSnelpw1 (synCsn C) (synCpw1 Q)
  have p0006 :=
    @gMpbir (.classMem (synCsn (synCsn C)) (synCpw1 (synCpw1 Q)))
      (.classMem (synCsn C) (synCpw1 Q)) p0004 p0005
  have p0007 := @gWpplitphnordpointfnfnndv
  have p0008 := @gFnfun (synCpw1 (synCvv)) (synCwpplitphnordpointfn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gSnex C
  have p0011 := @gSnelpw1 (synCsn C) (synCvv)
  have p0012 :=
    @gMpbir (.classMem (synCsn (synCsn C)) (synCpw1 (synCvv)))
      (.classMem (synCsn C) (synCvv)) p0010 p0011
  have p0014 := @gFndm (synCpw1 (synCvv)) (synCwpplitphnordpointfn)
  have p0015 := Nominal.mp p0007 p0014
  have p0016 :=
    @gEleq2i (synCdm (synCwpplitphnordpointfn)) (synCpw1 (synCvv))
      (synCsn (synCsn C)) p0015
  have p0017 :=
    @gMpbir (.classMem (synCsn (synCsn C)) (synCdm (synCwpplitphnordpointfn)))
      (.classMem (synCsn (synCsn C)) (synCpw1 (synCvv))) p0012 p0016
  have p0018 :=
    @gPm32i (synWfun (synCwpplitphnordpointfn))
      (.classMem (synCsn (synCsn C)) (synCdm (synCwpplitphnordpointfn))) p0009 p0017
  have p0019 :=
    @gFunfvima (synCpw1 (synCpw1 Q)) (synCsn (synCsn C)) (synCwpplitphnordpointfn)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := Nominal.mp p0006 p0020
  have p0022 :=
    @gEqeltri (synChnord C) (synCfv (synCwpplitphnordpointfn) (synCsn (synCsn C)))
      (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))) p0002 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordimssndv`. -/
@[expose]
noncomputable def gWpplitphnordimssndv (C : Class) (Q : Class)
    (_hyp_wpplitphnordimssndv_1 : Nominal.NPrf (.classMem Q (synCvv)))
    (hyp_wpplitphnordimssndv_2 : Nominal.NPrf (synWss Q (synCnc C))) :
    Nominal.NPrf
      (synWss (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q)))
        (synCnc (synChnord C))) :=
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
  have dv_cache_0001 : x ∉ ((synCpw1 (synCpw1 Q))).fv := by
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
  have dv_cache_0003 : x ∉ ((synCwpplitphnordpointfn)).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (synCnc (synChnord C)))).fv :=
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
    y ∉ ((synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q)))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCnc (synChnord C))).fv :=
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
  have p0000 := @gWpplitphnordpointfnfnndv
  have p0001 := @gSsv (synCpw1 Q)
  have p0002 := @gPw1ss (synCpw1 Q) (synCvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gPm32i (synWfn (synCwpplitphnordpointfn) (synCpw1 (synCvv)))
      (synWss (synCpw1 (synCpw1 Q)) (synCpw1 (synCvv))) p0000 p0003
  have p0005 :=
    @gFvelimab x (synCpw1 (synCvv)) (synCpw1 (synCpw1 Q)) (.cv y)
      (synCwpplitphnordpointfn) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gBiimpi
      (.classMem (.cv y) (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))))
      (synWrex x (synCpw1 (synCpw1 Q))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      p0006
  have p0008 :=
    @gSimpr (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0009 :=
    @gSimpl (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y))
  have p0010 := @gSsv Q
  have p0011 := @gPw1ss Q (synCvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gPw1ss (synCpw1 Q) (synCpw1 (synCvv))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gSseli (synCpw1 (synCpw1 Q)) (synCpw1 (synCpw1 (synCvv))) (.cv x) p0014
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (.classMem (.cv x) (synCpw1 (synCpw1 (synCvv)))) p0009 p0015
  have p0017 := @gWpplitphnordpointfnvalimpndv x
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCpw1 (synCvv))))
      (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x))
        (synChnord (synCuni (synCuni (.cv x)))))
      p0016 p0017
  have p0020 := @gFdcolcodearg Q x dv_cache_0004
  have p0021 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (synWa (.classMem (synCuni (synCuni (.cv x))) Q)
        (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x)))))))
      p0009 p0020
  have p0022 :=
    @gSimpl (.classMem (synCuni (synCuni (.cv x))) Q)
      (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x))))))
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (synWa (.classMem (synCuni (synCuni (.cv x))) Q)
        (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x)))))))
      (.classMem (synCuni (synCuni (.cv x))) Q) p0021 p0022
  have p0024 :=
    @gSseli Q (synCnc C) (synCuni (synCuni (.cv x))) hyp_wpplitphnordimssndv_2
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (synCuni (synCuni (.cv x))) Q)
      (.classMem (synCuni (synCuni (.cv x))) (synCnc C)) p0023 p0024
  have p0026 := @gHnordncmemimpndv C (synCuni (synCuni (.cv x)))
  have p0027 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (synCuni (synCuni (.cv x))) (synCnc C))
      (.classMem (synChnord (synCuni (synCuni (.cv x)))) (synCnc (synChnord C)))
      p0025 p0026
  have p0028 :=
    @gEqeltrd
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (synCfv (synCwpplitphnordpointfn) (.cv x))
      (synChnord (synCuni (synCuni (.cv x)))) (synCnc (synChnord C)) p0018 p0027
  have p0029 :=
    @gEqeltrrd
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y) (synCnc (synChnord C)) p0008
      p0028
  have p0030 :=
    @gRexlimiva (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y))
      (.classMem (.cv y) (synCnc (synChnord C))) x (synCpw1 (synCpw1 Q)) dv_cache_0005
      p0029
  have p0031 :=
    @gSyl
      (.classMem (.cv y) (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))))
      (synWrex x (synCpw1 (synCpw1 Q))
        (.classEq (synCfv (synCwpplitphnordpointfn) (.cv x)) (.cv y)))
      (.classMem (.cv y) (synCnc (synChnord C))) p0007 p0030
  have p0032 :=
    @gSsriv y (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q)))
      (synCnc (synChnord C)) dv_cache_0006 dv_cache_0007 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_wpplitphnordcardvalndv`. -/
@[expose]
noncomputable def gWpplitphnordcardvalndv (C : Class) (Q : Class)
    (hyp_wpplitphnordcardvalndv_1 : Nominal.NPrf (.classMem Q (synCvv)))
    (hyp_wpplitphnordcardvalndv_2 : Nominal.NPrf (.classMem C Q))
    (hyp_wpplitphnordcardvalndv_3 : Nominal.NPrf (synWss Q (synCnc C))) :
    Nominal.NPrf
      (.classEq (synCfv (synCimage (synCen))
          (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q)))) (synChncard C)) :=
  by
  have p0000 := @gEnex
  have p0001 := @gWpplitphnordimexndv Q hyp_wpplitphnordcardvalndv_1
  have p0002 :=
    @gFvimagecl (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))) (synCen)
      p0000 p0001
  have p0003 :=
    @gWpplitphnordimcanndv C Q hyp_wpplitphnordcardvalndv_1 hyp_wpplitphnordcardvalndv_2
  have p0004 :=
    @gWpplitphnordimssndv C Q hyp_wpplitphnordcardvalndv_1 hyp_wpplitphnordcardvalndv_3
  have p0005 :=
    @gEnimasatndv (synChnord C)
      (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))) p0003 p0004
  have p0006 :=
    @gEqtri
      (synCfv (synCimage (synCen))
        (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))))
      (synCima (synCen) (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))))
      (synCnc (synChnord C)) p0002 p0005
  have p0007 := (Nominal.classEqRefl (synChncard C))
  have p0008 := @gEqcomi (synChncard C) (synCnc (synChnord C)) p0007
  have p0009 :=
    @gEqtri
      (synCfv (synCimage (synCen))
        (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 Q))))
      (synCnc (synChnord C)) (synChncard C) p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2fnexndv`. -/
@[expose]
noncomputable def gWpppowset2fnexndv :
    Nominal.NPrf (.classMem (synCwpppowset2fn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowset2fn))
  have p0001 := @gWpppowsetfnexndv
  have p0003 := @gSiex (synCwpppowsetfn) p0001
  have p0004 := @gCoex (synCwpppowsetfn) (synCsi (synCwpppowsetfn)) p0001 p0003
  have p0005 :=
    @gEqeltri (synCwpppowset2fn)
      (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) (synCvv) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2fnfnndv`. -/
@[expose]
noncomputable def gWpppowset2fnfnndv :
    Nominal.NPrf (synWfn (synCwpppowset2fn) (synCpw1 (synCvv))) :=
  by
  have p0000 := @gWpppowsetfnfnndv
  have p0002 := @gSsv (synCrn (synCwpppowsetfn))
  have p0003 :=
    @gPm32i (synWfn (synCwpppowsetfn) (synCvv))
      (synWss (synCrn (synCwpppowsetfn)) (synCvv)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWf (synCwpppowsetfn) (synCvv) (synCvv)))
  have p0005 :=
    @gMpbir (synWf (synCwpppowsetfn) (synCvv) (synCvv))
      (synWa (synWfn (synCwpppowsetfn) (synCvv))
        (synWss (synCrn (synCwpppowsetfn)) (synCvv)))
      p0003 p0004
  have p0006 := @gSifmap (synCvv) (synCvv) (synCwpppowsetfn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gFfn (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCsi (synCwpppowsetfn))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gSsv (synCrn (synCsi (synCwpppowsetfn)))
  have p0011 :=
    @gN3pm32i (synWfn (synCwpppowsetfn) (synCvv))
      (synWfn (synCsi (synCwpppowsetfn)) (synCpw1 (synCvv)))
      (synWss (synCrn (synCsi (synCwpppowsetfn))) (synCvv)) p0000 p0009 p0010
  have p0012 :=
    @gFnco (synCvv) (synCpw1 (synCvv)) (synCwpppowsetfn) (synCsi (synCwpppowsetfn))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := (Nominal.classEqRefl (synCwpppowset2fn))
  have p0015 :=
    @gFneq1i (synCpw1 (synCvv)) (synCwpppowset2fn)
      (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) p0014
  have p0016 :=
    @gMpbir (synWfn (synCwpppowset2fn) (synCpw1 (synCvv)))
      (synWfn (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) (synCpw1 (synCvv)))
      p0013 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2fnvalndv`. -/
@[expose]
noncomputable def gWpppowset2fnvalndv (A : Class)
    (hyp_wpppowset2fnvalndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwpppowset2fn) (synCsn (synCsn A))) (synCpw (synCpw A))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpppowset2fn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn A)) (synCwpppowset2fn)
      (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) p0000
  have p0002 := @gWpppowsetfnfnndv
  have p0003 := @gSsv (synCrn (synCwpppowsetfn))
  have p0004 :=
    @gPm32i (synWfn (synCwpppowsetfn) (synCvv))
      (synWss (synCrn (synCwpppowsetfn)) (synCvv)) p0002 p0003
  have p0005 := (Nominal.biimpRefl (synWf (synCwpppowsetfn) (synCvv) (synCvv)))
  have p0006 :=
    @gMpbir (synWf (synCwpppowsetfn) (synCvv) (synCvv))
      (synWa (synWfn (synCwpppowsetfn) (synCvv))
        (synWss (synCrn (synCwpppowsetfn)) (synCvv)))
      p0004 p0005
  have p0007 := @gSifmap (synCvv) (synCvv) (synCwpppowsetfn)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gFfn (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCsi (synCwpppowsetfn))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gSnex A
  have p0012 := @gSnelpw1 (synCsn A) (synCvv)
  have p0013 :=
    @gMpbir (.classMem (synCsn (synCsn A)) (synCpw1 (synCvv)))
      (.classMem (synCsn A) (synCvv)) p0011 p0012
  have p0014 :=
    @gPm32i (synWfn (synCsi (synCwpppowsetfn)) (synCpw1 (synCvv)))
      (.classMem (synCsn (synCsn A)) (synCpw1 (synCvv))) p0010 p0013
  have p0015 :=
    @gFvco2 (synCpw1 (synCvv)) (synCsn (synCsn A)) (synCwpppowsetfn)
      (synCsi (synCwpppowsetfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0023 := @gSifvald (synCvv) (synCvv) (synCsn A) (synCwpppowsetfn) p0006
  have p0024 := Nominal.mp p0011 p0023
  have p0025 := @gWpppowsetfnvalndv A hyp_wpppowset2fnvalndv_1
  have p0026 := @gSneqi (synCfv (synCwpppowsetfn) (synCsn A)) (synCpw A) p0025
  have p0027 :=
    @gEqtri (synCfv (synCsi (synCwpppowsetfn)) (synCsn (synCsn A)))
      (synCsn (synCfv (synCwpppowsetfn) (synCsn A))) (synCsn (synCpw A)) p0024 p0026
  have p0028 :=
    @gFveq2i (synCfv (synCsi (synCwpppowsetfn)) (synCsn (synCsn A)))
      (synCsn (synCpw A)) (synCwpppowsetfn) p0027
  have p0029 :=
    @gEqtri
      (synCfv (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) (synCsn (synCsn A)))
      (synCfv (synCwpppowsetfn) (synCfv (synCsi (synCwpppowsetfn)) (synCsn (synCsn A))))
      (synCfv (synCwpppowsetfn) (synCsn (synCpw A))) p0016 p0028
  have p0030 := @gPwex A hyp_wpppowset2fnvalndv_1
  have p0031 := @gWpppowsetfnvalndv (synCpw A) p0030
  have p0032 :=
    @gEqtri
      (synCfv (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) (synCsn (synCsn A)))
      (synCfv (synCwpppowsetfn) (synCsn (synCpw A))) (synCpw (synCpw A)) p0029 p0031
  have p0033 :=
    @gEqtri (synCfv (synCwpppowset2fn) (synCsn (synCsn A)))
      (synCfv (synCcom (synCwpppowsetfn) (synCsi (synCwpppowsetfn))) (synCsn (synCsn A)))
      (synCpw (synCpw A)) p0001 p0032
  exact p0033

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2fnvalimpndv`. -/
@[expose]
noncomputable def gWpppowset2fnvalimpndv (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv))))
        (.classEq (synCfv (synCwpppowset2fn) (.cv q))
          (synCpw (synCpw (synCuni (synCuni (.cv q))))))) :=
  by
  have dv_cache_0001 : q ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gFdcolcodearg (synCvv) q dv_cache_0001
  have p0001 :=
    @gSimpr (.classMem (synCuni (synCuni (.cv q))) (synCvv))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
  have p0002 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) (synCvv))
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0000 p0001
  have p0003 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv)))) (.cv q)
      (synCsn (synCsn (synCuni (synCuni (.cv q))))) (synCwpppowset2fn) p0002
  have p0004 := @gVex q
  have p0005 := @gUniex (.cv q) p0004
  have p0006 := @gUniex (synCuni (.cv q)) p0005
  have p0007 := @gWpppowset2fnvalndv (synCuni (synCuni (.cv q))) p0006
  have p0008 :=
    @gA1i
      (.classEq (synCfv (synCwpppowset2fn) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
        (synCpw (synCpw (synCuni (synCuni (.cv q))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv)))) p0007
  have p0009 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCpw1 (synCvv))))
      (synCfv (synCwpppowset2fn) (.cv q))
      (synCfv (synCwpppowset2fn) (synCsn (synCsn (synCuni (synCuni (.cv q))))))
      (synCpw (synCpw (synCuni (synCuni (.cv q))))) p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2imexndv`. -/
@[expose]
noncomputable def gWpppowset2imexndv (Q : Class)
    (hyp_wpppowset2imexndv_1 : Nominal.NPrf (.classMem Q (synCvv))) :
    Nominal.NPrf
      (.classMem (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q))) (synCvv)) :=
  by
  have p0000 := @gWpppowset2fnexndv
  have p0001 := @gPw1ex Q hyp_wpppowset2imexndv_1
  have p0002 := @gPw1ex (synCpw1 Q) p0001
  have p0003 := @gImaex (synCwpppowset2fn) (synCpw1 (synCpw1 Q)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2imcanndv`. -/
@[expose]
noncomputable def gWpppowset2imcanndv (C : Class) (Q : Class)
    (_hyp_wpppowset2imcanndv_1 : Nominal.NPrf (.classMem Q (synCvv)))
    (hyp_wpppowset2imcanndv_2 : Nominal.NPrf (.classMem C Q)) :
    Nominal.NPrf
      (.classMem (synCpw (synCpw C))
        (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q)))) :=
  by
  have p0000 := @gElexi C Q hyp_wpppowset2imcanndv_2
  have p0001 := @gWpppowset2fnvalndv C p0000
  have p0002 :=
    @gEqcomi (synCfv (synCwpppowset2fn) (synCsn (synCsn C))) (synCpw (synCpw C))
      p0001
  have p0003 := @gSnelpw1 C Q
  have p0004 :=
    @gMpbir (.classMem (synCsn C) (synCpw1 Q)) (.classMem C Q) hyp_wpppowset2imcanndv_2
      p0003
  have p0005 := @gSnelpw1 (synCsn C) (synCpw1 Q)
  have p0006 :=
    @gMpbir (.classMem (synCsn (synCsn C)) (synCpw1 (synCpw1 Q)))
      (.classMem (synCsn C) (synCpw1 Q)) p0004 p0005
  have p0007 := @gWpppowset2fnfnndv
  have p0008 := @gFnfun (synCpw1 (synCvv)) (synCwpppowset2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gSnex C
  have p0011 := @gSnelpw1 (synCsn C) (synCvv)
  have p0012 :=
    @gMpbir (.classMem (synCsn (synCsn C)) (synCpw1 (synCvv)))
      (.classMem (synCsn C) (synCvv)) p0010 p0011
  have p0014 := @gFndm (synCpw1 (synCvv)) (synCwpppowset2fn)
  have p0015 := Nominal.mp p0007 p0014
  have p0016 :=
    @gEleq2i (synCdm (synCwpppowset2fn)) (synCpw1 (synCvv)) (synCsn (synCsn C))
      p0015
  have p0017 :=
    @gMpbir (.classMem (synCsn (synCsn C)) (synCdm (synCwpppowset2fn)))
      (.classMem (synCsn (synCsn C)) (synCpw1 (synCvv))) p0012 p0016
  have p0018 :=
    @gPm32i (synWfun (synCwpppowset2fn))
      (.classMem (synCsn (synCsn C)) (synCdm (synCwpppowset2fn))) p0009 p0017
  have p0019 :=
    @gFunfvima (synCpw1 (synCpw1 Q)) (synCsn (synCsn C)) (synCwpppowset2fn)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := Nominal.mp p0006 p0020
  have p0022 :=
    @gEqeltri (synCpw (synCpw C)) (synCfv (synCwpppowset2fn) (synCsn (synCsn C)))
      (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q))) p0002 p0021
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

/-- Checked nominal proof certificate identified upstream as `g_wpppowset2imssndv`. -/
@[expose]
noncomputable def gWpppowset2imssndv (C : Class) (Q : Class)
    (_hyp_wpppowset2imssndv_1 : Nominal.NPrf (.classMem Q (synCvv)))
    (hyp_wpppowset2imssndv_2 : Nominal.NPrf (synWss Q (synCnc C))) :
    Nominal.NPrf
      (synWss (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q)))
        (synCnc (synCpw (synCpw C)))) :=
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
  have dv_cache_0001 : x ∉ ((synCpw1 (synCpw1 Q))).fv := by
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
  have dv_cache_0003 : x ∉ ((synCwpppowset2fn)).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) (synCnc (synCpw (synCpw C))))).fv :=
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
  have dv_cache_0006 : y ∉ ((synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q)))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCnc (synCpw (synCpw C)))).fv :=
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
  have p0000 := @gWpppowset2fnfnndv
  have p0001 := @gSsv (synCpw1 Q)
  have p0002 := @gPw1ss (synCpw1 Q) (synCvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gPm32i (synWfn (synCwpppowset2fn) (synCpw1 (synCvv)))
      (synWss (synCpw1 (synCpw1 Q)) (synCpw1 (synCvv))) p0000 p0003
  have p0005 :=
    @gFvelimab x (synCpw1 (synCvv)) (synCpw1 (synCpw1 Q)) (.cv y) (synCwpppowset2fn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gBiimpi (.classMem (.cv y) (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q))))
      (synWrex x (synCpw1 (synCpw1 Q))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      p0006
  have p0008 :=
    @gSimpr (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y))
  have p0009 :=
    @gSimpl (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y))
  have p0010 := @gSsv Q
  have p0011 := @gPw1ss Q (synCvv)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 := @gPw1ss (synCpw1 Q) (synCpw1 (synCvv))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gSseli (synCpw1 (synCpw1 Q)) (synCpw1 (synCpw1 (synCvv))) (.cv x) p0014
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (.classMem (.cv x) (synCpw1 (synCpw1 (synCvv)))) p0009 p0015
  have p0017 := @gWpppowset2fnvalimpndv x
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCpw1 (synCvv))))
      (.classEq (synCfv (synCwpppowset2fn) (.cv x))
        (synCpw (synCpw (synCuni (synCuni (.cv x))))))
      p0016 p0017
  have p0020 := @gFdcolcodearg Q x dv_cache_0004
  have p0021 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
      (synWa (.classMem (synCuni (synCuni (.cv x))) Q)
        (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x)))))))
      p0009 p0020
  have p0022 :=
    @gSimpl (.classMem (synCuni (synCuni (.cv x))) Q)
      (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x))))))
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (synWa (.classMem (synCuni (synCuni (.cv x))) Q)
        (.classEq (.cv x) (synCsn (synCsn (synCuni (synCuni (.cv x)))))))
      (.classMem (synCuni (synCuni (.cv x))) Q) p0021 p0022
  have p0024 :=
    @gSseli Q (synCnc C) (synCuni (synCuni (.cv x))) hyp_wpppowset2imssndv_2
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (synCuni (synCuni (.cv x))) Q)
      (.classMem (synCuni (synCuni (.cv x))) (synCnc C)) p0023 p0024
  have p0026 := @gElnc (synCuni (synCuni (.cv x))) C
  have p0027 :=
    @gSylib
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (synCuni (synCuni (.cv x))) (synCnc C))
      (synWbr (synCuni (synCuni (.cv x))) (synCen) C) p0025 p0026
  have p0028 := @gEnpw (synCuni (synCuni (.cv x))) C
  have p0029 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (synWbr (synCuni (synCuni (.cv x))) (synCen) C)
      (synWbr (synCpw (synCuni (synCuni (.cv x)))) (synCen) (synCpw C)) p0027 p0028
  have p0030 := @gEnpw (synCpw (synCuni (synCuni (.cv x)))) (synCpw C)
  have p0031 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (synWbr (synCpw (synCuni (synCuni (.cv x)))) (synCen) (synCpw C))
      (synWbr (synCpw (synCpw (synCuni (synCuni (.cv x))))) (synCen)
        (synCpw (synCpw C)))
      p0029 p0030
  have p0032 :=
    @gElnc (synCpw (synCpw (synCuni (synCuni (.cv x))))) (synCpw (synCpw C))
  have p0033 :=
    @gSylibr
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (synWbr (synCpw (synCpw (synCuni (synCuni (.cv x))))) (synCen)
        (synCpw (synCpw C)))
      (.classMem (synCpw (synCpw (synCuni (synCuni (.cv x)))))
        (synCnc (synCpw (synCpw C))))
      p0031 p0032
  have p0034 :=
    @gEqeltrd
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (synCfv (synCwpppowset2fn) (.cv x))
      (synCpw (synCpw (synCuni (synCuni (.cv x))))) (synCnc (synCpw (synCpw C)))
      p0018 p0033
  have p0035 :=
    @gEqeltrrd
      (synWa (.classMem (.cv x) (synCpw1 (synCpw1 Q)))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (synCfv (synCwpppowset2fn) (.cv x)) (.cv y) (synCnc (synCpw (synCpw C))) p0008
      p0034
  have p0036 :=
    @gRexlimiva (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y))
      (.classMem (.cv y) (synCnc (synCpw (synCpw C)))) x (synCpw1 (synCpw1 Q))
      dv_cache_0005 p0035
  have p0037 :=
    @gSyl (.classMem (.cv y) (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q))))
      (synWrex x (synCpw1 (synCpw1 Q))
        (.classEq (synCfv (synCwpppowset2fn) (.cv x)) (.cv y)))
      (.classMem (.cv y) (synCnc (synCpw (synCpw C)))) p0007 p0036
  have p0038 :=
    @gSsriv y (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q)))
      (synCnc (synCpw (synCpw C))) dv_cache_0006 dv_cache_0007 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_sif1mapndv`. -/
@[expose]
noncomputable def gSif1mapndv (A : Class) (B : Class) (F : Class)
    (hyp_sif1mapndv_1 : Nominal.NPrf (synWf1 F A B)) :
    Nominal.NPrf (synWf1 (synCsi F) (synCpw1 A) (synCpw1 B)) :=
  by
  have p0000 := @gF1f A B F
  have p0001 := Nominal.mp hyp_sif1mapndv_1 p0000
  have p0002 := @gSifmap A B F
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := (Nominal.biimpRefl (synWf1 F A B))
  have p0005 :=
    @gMpbi (synWf1 F A B) (synWa (synWf F A B) (synWfun (synCcnv F)))
      hyp_sif1mapndv_1 p0004
  have p0006 := @gSimpri (synWf F A B) (synWfun (synCcnv F)) p0005
  have p0007 := @gFunsi (synCcnv F)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gCnvsi F
  have p0010 := @gFuneqi (synCcnv (synCsi F)) (synCsi (synCcnv F)) p0009
  have p0011 :=
    @gMpbir (synWfun (synCcnv (synCsi F))) (synWfun (synCsi (synCcnv F))) p0008
      p0010
  have p0012 :=
    @gPm32i (synWf (synCsi F) (synCpw1 A) (synCpw1 B))
      (synWfun (synCcnv (synCsi F))) p0003 p0011
  have p0013 := (Nominal.biimpRefl (synWf1 (synCsi F) (synCpw1 A) (synCpw1 B)))
  have p0014 :=
    @gMpbir (synWf1 (synCsi F) (synCpw1 A) (synCpw1 B))
      (synWa (synWf (synCsi F) (synCpw1 A) (synCpw1 B)) (synWfun (synCcnv (synCsi F))))
      p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_wppcardt2fnf1ndv`. -/
@[expose]
noncomputable def gWppcardt2fnf1ndv :
    Nominal.NPrf
      (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs)) :=
  by
  have p0000 := @gWppcardtfnf1ndv
  have p0002 := @gSif1mapndv (synCpw1 (synCncs)) (synCncs) (synCwppcardtfn) p0000
  have p0003 :=
    @gPm32i (synWf1 (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
      (synWf1 (synCsi (synCwppcardtfn)) (synCpw1 (synCpw1 (synCncs)))
        (synCpw1 (synCncs)))
      p0000 p0002
  have p0004 :=
    @gF1co (synCpw1 (synCpw1 (synCncs))) (synCpw1 (synCncs)) (synCncs)
      (synCwppcardtfn) (synCsi (synCwppcardtfn))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := (Nominal.classEqRefl (synCwppcardt2fn))
  have p0007 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gMpbir (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf1 (synCcom (synCwppcardtfn) (synCsi (synCwppcardtfn)))
        (synCpw1 (synCpw1 (synCncs))) (synCncs))
      p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wppcardt4fnf1ndv`. -/
@[expose]
noncomputable def gWppcardt4fnf1ndv :
    Nominal.NPrf
      (synWf1 (synCwppcardt4fn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
        (synCncs)) :=
  by
  have p0000 := @gWppcardt2fnf1ndv
  have p0002 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn) p0000
  have p0003 :=
    @gSif1mapndv (synCpw1 (synCpw1 (synCpw1 (synCncs)))) (synCpw1 (synCncs))
      (synCsi (synCwppcardt2fn)) p0002
  have p0004 :=
    @gPm32i (synWf1 (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf1 (synCsi (synCsi (synCwppcardt2fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCpw1 (synCpw1 (synCncs))))
      p0000 p0003
  have p0005 :=
    @gF1co (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt2fn)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := (Nominal.classEqRefl (synCwppcardt4fn))
  have p0008 :=
    @gF1eq1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gMpbir
      (synWf1 (synCwppcardt4fn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))
        (synCncs))
      (synWf1 (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt2fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs))
      p0006 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wppfamilyrep2fnexndv`. -/
@[expose]
noncomputable def gWppfamilyrep2fnexndv :
    Nominal.NPrf (.classMem (synCwppfamilyrep2fn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppfamilyrep2fn))
  have p0001 := @gVvex
  have p0002 := @gFdpointrelex (synCvv) p0001
  have p0003 := @gImageex (synCfdpointrel (synCvv)) p0002
  have p0004 :=
    @gEqeltri (synCwppfamilyrep2fn) (synCimage (synCfdpointrel (synCvv))) (synCvv)
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wppfamilyrep2fnfnndv`. -/
@[expose]
noncomputable def gWppfamilyrep2fnfnndv :
    Nominal.NPrf (synWfn (synCwppfamilyrep2fn) (synCvv)) :=
  by
  have p0000 := @gVvex
  have p0001 := @gFdpointrelex (synCvv) p0000
  have p0002 := @gWppimagefn (synCfdpointrel (synCvv)) p0001
  have p0003 := (Nominal.classEqRefl (synCwppfamilyrep2fn))
  have p0004 :=
    @gFneq1i (synCvv) (synCwppfamilyrep2fn) (synCimage (synCfdpointrel (synCvv)))
      p0003
  have p0005 :=
    @gMpbir (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWfn (synCimage (synCfdpointrel (synCvv))) (synCvv)) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppfamilyrep2fnvalndv`. -/
@[expose]
noncomputable def gWppfamilyrep2fnvalndv (Q : Class)
    (hyp_wppfamilyrep2fnvalndv_1 : Nominal.NPrf (.classMem Q (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppfamilyrep2fn) (synCsn (synCsn Q)))
        (synCpw1 (synCpw1 Q))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppfamilyrep2fn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn Q)) (synCwppfamilyrep2fn)
      (synCimage (synCfdpointrel (synCvv))) p0000
  have p0002 := @gVvex
  have p0003 := @gFdpointrelex (synCvv) p0002
  have p0004 := @gSnex (synCsn Q)
  have p0005 := @gFvimagecl (synCsn (synCsn Q)) (synCfdpointrel (synCvv)) p0003 p0004
  have p0006 := @gFdpointimagevvdndv Q
  have p0007 := Nominal.mp hyp_wppfamilyrep2fnvalndv_1 p0006
  have p0008 :=
    @gEqtri (synCfv (synCimage (synCfdpointrel (synCvv))) (synCsn (synCsn Q)))
      (synCima (synCfdpointrel (synCvv)) (synCsn (synCsn Q))) (synCpw1 (synCpw1 Q))
      p0005 p0007
  have p0009 :=
    @gEqtri (synCfv (synCwppfamilyrep2fn) (synCsn (synCsn Q)))
      (synCfv (synCimage (synCfdpointrel (synCvv))) (synCsn (synCsn Q)))
      (synCpw1 (synCpw1 Q)) p0001 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wppdirecte2famfnexndv`. -/
@[expose]
noncomputable def gWppdirecte2famfnexndv :
    Nominal.NPrf (.classMem (synCwppdirecte2famfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppdirecte2famfn))
  have p0001 := @gWpppowset2fnexndv
  have p0002 := @gImageex (synCwpppowset2fn) p0001
  have p0003 := @gWppfamilyrep2fnexndv
  have p0004 :=
    @gCoex (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn) p0002 p0003
  have p0005 :=
    @gEqeltri (synCwppdirecte2famfn)
      (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn)) (synCvv) p0000
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppdirecte2famfnfnndv`. -/
@[expose]
noncomputable def gWppdirecte2famfnfnndv :
    Nominal.NPrf (synWfn (synCwppdirecte2famfn) (synCvv)) :=
  by
  have p0000 := @gWpppowset2fnexndv
  have p0001 := @gWppimagefn (synCwpppowset2fn) p0000
  have p0002 := @gWppfamilyrep2fnfnndv
  have p0003 := @gDffn2 (synCvv) (synCwppfamilyrep2fn)
  have p0004 :=
    @gMpbi (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0002 p0003
  have p0005 :=
    @gPm32i (synWfn (synCimage (synCwpppowset2fn)) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0001 p0004
  have p0006 :=
    @gFnfco (synCvv) (synCvv) (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := (Nominal.classEqRefl (synCwppdirecte2famfn))
  have p0009 :=
    @gFneq1i (synCvv) (synCwppdirecte2famfn)
      (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn)) p0008
  have p0010 :=
    @gMpbir (synWfn (synCwppdirecte2famfn) (synCvv))
      (synWfn (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn)) (synCvv))
      p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wppdirecte2famfnvalndv`. -/
@[expose]
noncomputable def gWppdirecte2famfnvalndv (Q : Class)
    (hyp_wppdirecte2famfnvalndv_1 : Nominal.NPrf (.classMem Q (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppdirecte2famfn) (synCsn (synCsn Q)))
        (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppdirecte2famfn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn Q)) (synCwppdirecte2famfn)
      (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn)) p0000
  have p0002 := @gWppfamilyrep2fnfnndv
  have p0003 := @gSnex (synCsn Q)
  have p0004 :=
    @gPm32i (synWfn (synCwppfamilyrep2fn) (synCvv))
      (.classMem (synCsn (synCsn Q)) (synCvv)) p0002 p0003
  have p0005 :=
    @gFvco2 (synCvv) (synCsn (synCsn Q)) (synCimage (synCwpppowset2fn))
      (synCwppfamilyrep2fn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gWppfamilyrep2fnvalndv Q hyp_wppdirecte2famfnvalndv_1
  have p0008 :=
    @gFveq2i (synCfv (synCwppfamilyrep2fn) (synCsn (synCsn Q)))
      (synCpw1 (synCpw1 Q)) (synCimage (synCwpppowset2fn)) p0007
  have p0009 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn Q)))
      (synCfv (synCimage (synCwpppowset2fn))
        (synCfv (synCwppfamilyrep2fn) (synCsn (synCsn Q))))
      (synCfv (synCimage (synCwpppowset2fn)) (synCpw1 (synCpw1 Q))) p0006 p0008
  have p0010 := @gWpppowset2fnexndv
  have p0011 := @gPw1ex Q hyp_wppdirecte2famfnvalndv_1
  have p0012 := @gPw1ex (synCpw1 Q) p0011
  have p0013 := @gFvimagecl (synCpw1 (synCpw1 Q)) (synCwpppowset2fn) p0010 p0012
  have p0014 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn Q)))
      (synCfv (synCimage (synCwpppowset2fn)) (synCpw1 (synCpw1 Q)))
      (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q))) p0009 p0013
  have p0015 :=
    @gEqtri (synCfv (synCwppdirecte2famfn) (synCsn (synCsn Q)))
      (synCfv (synCcom (synCimage (synCwpppowset2fn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn Q)))
      (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 Q))) p0001 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wppdirecth1famfnexndv`. -/
@[expose]
noncomputable def gWppdirecth1famfnexndv :
    Nominal.NPrf (.classMem (synCwppdirecth1famfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppdirecth1famfn))
  have p0001 := @gWpplitphnordpointfnexndv
  have p0002 := @gImageex (synCwpplitphnordpointfn) p0001
  have p0003 := @gWppfamilyrep2fnexndv
  have p0004 :=
    @gCoex (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn) p0002 p0003
  have p0005 := @gWppdirecte2famfnexndv
  have p0006 := @gSiex (synCwppdirecte2famfn) p0005
  have p0007 := @gSiex (synCsi (synCwppdirecte2famfn)) p0006
  have p0008 :=
    @gCoex (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecte2famfn))) p0004 p0007
  have p0009 :=
    @gEqeltri (synCwppdirecth1famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecte2famfn))))
      (synCvv) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wppdirecth1famfnfnndv`. -/
@[expose]
noncomputable def gWppdirecth1famfnfnndv :
    Nominal.NPrf (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv)))) :=
  by
  have p0000 := @gWpplitphnordpointfnexndv
  have p0001 := @gWppimagefn (synCwpplitphnordpointfn) p0000
  have p0002 := @gWppfamilyrep2fnfnndv
  have p0003 := @gDffn2 (synCvv) (synCwppfamilyrep2fn)
  have p0004 :=
    @gMpbi (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0002 p0003
  have p0005 :=
    @gPm32i (synWfn (synCimage (synCwpplitphnordpointfn)) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0001 p0004
  have p0006 :=
    @gFnfco (synCvv) (synCvv) (synCimage (synCwpplitphnordpointfn))
      (synCwppfamilyrep2fn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gWppdirecte2famfnfnndv
  have p0009 := @gDffn2 (synCvv) (synCwppdirecte2famfn)
  have p0010 :=
    @gMpbi (synWfn (synCwppdirecte2famfn) (synCvv))
      (synWf (synCwppdirecte2famfn) (synCvv) (synCvv)) p0008 p0009
  have p0011 := @gSifmap (synCvv) (synCvv) (synCwppdirecte2famfn)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gSifmap (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCsi (synCwppdirecte2famfn))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gFfn (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))
      (synCsi (synCsi (synCwppdirecte2famfn)))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gDffn2 (synCpw1 (synCpw1 (synCvv))) (synCsi (synCsi (synCwppdirecte2famfn)))
  have p0018 :=
    @gMpbi
      (synWfn (synCsi (synCsi (synCwppdirecte2famfn))) (synCpw1 (synCpw1 (synCvv))))
      (synWf (synCsi (synCsi (synCwppdirecte2famfn))) (synCpw1 (synCpw1 (synCvv)))
        (synCvv))
      p0016 p0017
  have p0019 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCvv))
      (synWf (synCsi (synCsi (synCwppdirecte2famfn))) (synCpw1 (synCpw1 (synCvv)))
        (synCvv))
      p0007 p0018
  have p0020 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCvv)))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecte2famfn)))
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := (Nominal.classEqRefl (synCwppdirecth1famfn))
  have p0023 :=
    @gFneq1i (synCpw1 (synCpw1 (synCvv))) (synCwppdirecth1famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecte2famfn))))
      p0022
  have p0024 :=
    @gMpbir (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))))
      (synWfn (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecte2famfn)))) (synCpw1 (synCpw1 (synCvv))))
      p0021 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_wppdirecth1famfnvalndv`. -/
@[expose]
noncomputable def gWppdirecth1famfnvalndv (Q : Class)
    (hyp_wppdirecth1famfnvalndv_1 : Nominal.NPrf (.classMem Q (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppdirecth1famfn) (synCsn (synCsn Q)))
        (synCima (synCwpplitphnordpointfn)
          (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppdirecth1famfn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn Q)) (synCwppdirecth1famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecte2famfn))))
      p0000
  have p0002 := @gWppdirecte2famfnfnndv
  have p0003 := @gDffn2 (synCvv) (synCwppdirecte2famfn)
  have p0004 :=
    @gMpbi (synWfn (synCwppdirecte2famfn) (synCvv))
      (synWf (synCwppdirecte2famfn) (synCvv) (synCvv)) p0002 p0003
  have p0005 := @gSifmap (synCvv) (synCvv) (synCwppdirecte2famfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gSifmap (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCsi (synCwppdirecte2famfn))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gFfn (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synCpw1 (synCvv)))
      (synCsi (synCsi (synCwppdirecte2famfn)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gSnelpw1 Q (synCvv)
  have p0012 :=
    @gMpbir (.classMem (synCsn Q) (synCpw1 (synCvv))) (.classMem Q (synCvv))
      hyp_wppdirecth1famfnvalndv_1 p0011
  have p0013 := @gSnelpw1 (synCsn Q) (synCpw1 (synCvv))
  have p0014 :=
    @gMpbir (.classMem (synCsn (synCsn Q)) (synCpw1 (synCpw1 (synCvv))))
      (.classMem (synCsn Q) (synCpw1 (synCvv))) p0012 p0013
  have p0015 :=
    @gPm32i
      (synWfn (synCsi (synCsi (synCwppdirecte2famfn))) (synCpw1 (synCpw1 (synCvv))))
      (.classMem (synCsn (synCsn Q)) (synCpw1 (synCpw1 (synCvv)))) p0010 p0014
  have p0016 :=
    @gFvco2 (synCpw1 (synCpw1 (synCvv))) (synCsn (synCsn Q))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecte2famfn)))
  have p0017 := Nominal.mp p0015 p0016
  have p0025 :=
    @gSifvald (synCpw1 (synCvv)) (synCpw1 (synCvv)) (synCsn Q)
      (synCsi (synCwppdirecte2famfn)) p0006
  have p0026 := Nominal.mp p0012 p0025
  have p0030 := @gSifvald (synCvv) (synCvv) Q (synCwppdirecte2famfn) p0004
  have p0031 := Nominal.mp hyp_wppdirecth1famfnvalndv_1 p0030
  have p0032 :=
    @gSneqi (synCfv (synCsi (synCwppdirecte2famfn)) (synCsn Q))
      (synCsn (synCfv (synCwppdirecte2famfn) Q)) p0031
  have p0033 :=
    @gEqtri (synCfv (synCsi (synCsi (synCwppdirecte2famfn))) (synCsn (synCsn Q)))
      (synCsn (synCfv (synCsi (synCwppdirecte2famfn)) (synCsn Q)))
      (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))) p0026 p0032
  have p0034 :=
    @gFveq2i (synCfv (synCsi (synCsi (synCwppdirecte2famfn))) (synCsn (synCsn Q)))
      (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q)))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn)) p0033
  have p0035 :=
    @gEqtri
      (synCfv (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecte2famfn)))) (synCsn (synCsn Q)))
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCfv (synCsi (synCsi (synCwppdirecte2famfn))) (synCsn (synCsn Q))))
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))))
      p0017 p0034
  have p0036 := @gWppfamilyrep2fnfnndv
  have p0037 := @gSnex (synCsn (synCfv (synCwppdirecte2famfn) Q))
  have p0038 :=
    @gPm32i (synWfn (synCwppfamilyrep2fn) (synCvv))
      (.classMem (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))) (synCvv)) p0036
      p0037
  have p0039 :=
    @gFvco2 (synCvv) (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q)))
      (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn)
  have p0040 := Nominal.mp p0038 p0039
  have p0041 := @gFvex Q (synCwppdirecte2famfn)
  have p0042 := @gWppfamilyrep2fnvalndv (synCfv (synCwppdirecte2famfn) Q) p0041
  have p0043 :=
    @gFveq2i
      (synCfv (synCwppfamilyrep2fn) (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))))
      (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q)))
      (synCimage (synCwpplitphnordpointfn)) p0042
  have p0044 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))))
      (synCfv (synCimage (synCwpplitphnordpointfn)) (synCfv (synCwppfamilyrep2fn)
          (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q)))))
      (synCfv (synCimage (synCwpplitphnordpointfn))
        (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q))))
      p0040 p0043
  have p0045 := @gWpplitphnordpointfnexndv
  have p0047 := @gPw1ex (synCfv (synCwppdirecte2famfn) Q) p0041
  have p0048 := @gPw1ex (synCpw1 (synCfv (synCwppdirecte2famfn) Q)) p0047
  have p0049 :=
    @gFvimagecl (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q)))
      (synCwpplitphnordpointfn) p0045 p0048
  have p0050 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))))
      (synCfv (synCimage (synCwpplitphnordpointfn))
        (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q))))
      (synCima (synCwpplitphnordpointfn)
        (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q))))
      p0044 p0049
  have p0051 :=
    @gEqtri
      (synCfv (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecte2famfn)))) (synCsn (synCsn Q)))
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecte2famfn) Q))))
      (synCima (synCwpplitphnordpointfn)
        (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q))))
      p0035 p0050
  have p0052 :=
    @gEqtri (synCfv (synCwppdirecth1famfn) (synCsn (synCsn Q)))
      (synCfv (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecte2famfn)))) (synCsn (synCsn Q)))
      (synCima (synCwpplitphnordpointfn)
        (synCpw1 (synCpw1 (synCfv (synCwppdirecte2famfn) Q))))
      p0001 p0051
  exact p0052

/-- Checked nominal proof certificate identified upstream as `g_wppdirecth2famfnvalndv`. -/
@[expose]
noncomputable def gWppdirecth2famfnvalndv (Q : Class)
    (hyp_wppdirecth2famfnvalndv_1 :
      Nominal.NPrf (.classMem Q (synCpw1 (synCpw1 (synCvv))))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppdirecth2famfn) (synCsn (synCsn Q)))
        (synCima (synCwpplitphnordpointfn)
          (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppdirecth2famfn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn Q)) (synCwppdirecth2famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecth1famfn))))
      p0000
  have p0002 := @gWppdirecth1famfnfnndv
  have p0003 := @gDffn2 (synCpw1 (synCpw1 (synCvv))) (synCwppdirecth1famfn)
  have p0004 :=
    @gMpbi (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))))
      (synWf (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))) (synCvv)) p0002
      p0003
  have p0005 :=
    @gSifmap (synCpw1 (synCpw1 (synCvv))) (synCvv) (synCwppdirecth1famfn)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCvv)))) (synCpw1 (synCvv))
      (synCsi (synCwppdirecth1famfn))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCpw1 (synCpw1 (synCvv))) (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 := @gSnelpw1 Q (synCpw1 (synCpw1 (synCvv)))
  have p0012 :=
    @gMpbir (.classMem (synCsn Q) (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (.classMem Q (synCpw1 (synCpw1 (synCvv)))) hyp_wppdirecth2famfnvalndv_1 p0011
  have p0013 := @gSnelpw1 (synCsn Q) (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0014 :=
    @gMpbir
      (.classMem (synCsn (synCsn Q)) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (.classMem (synCsn Q) (synCpw1 (synCpw1 (synCpw1 (synCvv))))) p0012 p0013
  have p0015 :=
    @gPm32i
      (synWfn (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (.classMem (synCsn (synCsn Q)) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0010 p0014
  have p0016 :=
    @gFvco2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCsn (synCsn Q))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0017 := Nominal.mp p0015 p0016
  have p0025 :=
    @gSifvald (synCpw1 (synCpw1 (synCpw1 (synCvv)))) (synCpw1 (synCvv)) (synCsn Q)
      (synCsi (synCwppdirecth1famfn)) p0006
  have p0026 := Nominal.mp p0012 p0025
  have p0030 :=
    @gSifvald (synCpw1 (synCpw1 (synCvv))) (synCvv) Q (synCwppdirecth1famfn) p0004
  have p0031 := Nominal.mp hyp_wppdirecth2famfnvalndv_1 p0030
  have p0032 :=
    @gSneqi (synCfv (synCsi (synCwppdirecth1famfn)) (synCsn Q))
      (synCsn (synCfv (synCwppdirecth1famfn) Q)) p0031
  have p0033 :=
    @gEqtri (synCfv (synCsi (synCsi (synCwppdirecth1famfn))) (synCsn (synCsn Q)))
      (synCsn (synCfv (synCsi (synCwppdirecth1famfn)) (synCsn Q)))
      (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))) p0026 p0032
  have p0034 :=
    @gFveq2i (synCfv (synCsi (synCsi (synCwppdirecth1famfn))) (synCsn (synCsn Q)))
      (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q)))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn)) p0033
  have p0035 :=
    @gEqtri
      (synCfv (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn)))) (synCsn (synCsn Q)))
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCfv (synCsi (synCsi (synCwppdirecth1famfn))) (synCsn (synCsn Q))))
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))))
      p0017 p0034
  have p0036 := @gWppfamilyrep2fnfnndv
  have p0037 := @gSnex (synCsn (synCfv (synCwppdirecth1famfn) Q))
  have p0038 :=
    @gPm32i (synWfn (synCwppfamilyrep2fn) (synCvv))
      (.classMem (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))) (synCvv)) p0036
      p0037
  have p0039 :=
    @gFvco2 (synCvv) (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q)))
      (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn)
  have p0040 := Nominal.mp p0038 p0039
  have p0041 := @gFvex Q (synCwppdirecth1famfn)
  have p0042 := @gWppfamilyrep2fnvalndv (synCfv (synCwppdirecth1famfn) Q) p0041
  have p0043 :=
    @gFveq2i
      (synCfv (synCwppfamilyrep2fn) (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))))
      (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q)))
      (synCimage (synCwpplitphnordpointfn)) p0042
  have p0044 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))))
      (synCfv (synCimage (synCwpplitphnordpointfn)) (synCfv (synCwppfamilyrep2fn)
          (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q)))))
      (synCfv (synCimage (synCwpplitphnordpointfn))
        (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q))))
      p0040 p0043
  have p0045 := @gWpplitphnordpointfnexndv
  have p0047 := @gPw1ex (synCfv (synCwppdirecth1famfn) Q) p0041
  have p0048 := @gPw1ex (synCpw1 (synCfv (synCwppdirecth1famfn) Q)) p0047
  have p0049 :=
    @gFvimagecl (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q)))
      (synCwpplitphnordpointfn) p0045 p0048
  have p0050 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))))
      (synCfv (synCimage (synCwpplitphnordpointfn))
        (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q))))
      (synCima (synCwpplitphnordpointfn)
        (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q))))
      p0044 p0049
  have p0051 :=
    @gEqtri
      (synCfv (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn)))) (synCsn (synCsn Q)))
      (synCfv (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsn (synCsn (synCfv (synCwppdirecth1famfn) Q))))
      (synCima (synCwpplitphnordpointfn)
        (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q))))
      p0035 p0050
  have p0052 :=
    @gEqtri (synCfv (synCwppdirecth2famfn) (synCsn (synCsn Q)))
      (synCfv (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn)))) (synCsn (synCsn Q)))
      (synCima (synCwpplitphnordpointfn)
        (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn) Q))))
      p0001 p0051
  exact p0052

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6codefnvalndv`. -/
@[expose]
noncomputable def gWppconcrete6codefnvalndv (X : Class)
    (hyp_wppconcrete6codefnvalndv_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.classEq (synCfv (synCwppconcrete6codefn)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
        (synChncard (synChnord (synCpw (synCpw X))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppconcrete6codefn))
  have p0001 :=
    @gFveq1i (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
      (synCwppconcrete6codefn) (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
      p0000
  have p0002 := @gWpplitphnordpointfnexndv
  have p0003 := @gWppimagefn (synCwpplitphnordpointfn) p0002
  have p0004 := @gWppfamilyrep2fnfnndv
  have p0005 := @gDffn2 (synCvv) (synCwppfamilyrep2fn)
  have p0006 :=
    @gMpbi (synWfn (synCwppfamilyrep2fn) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0004 p0005
  have p0007 :=
    @gPm32i (synWfn (synCimage (synCwpplitphnordpointfn)) (synCvv))
      (synWf (synCwppfamilyrep2fn) (synCvv) (synCvv)) p0003 p0006
  have p0008 :=
    @gFnfco (synCvv) (synCvv) (synCimage (synCwpplitphnordpointfn))
      (synCwppfamilyrep2fn)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 := @gWppdirecth1famfnfnndv
  have p0011 := @gDffn2 (synCpw1 (synCpw1 (synCvv))) (synCwppdirecth1famfn)
  have p0012 :=
    @gMpbi (synWfn (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))))
      (synWf (synCwppdirecth1famfn) (synCpw1 (synCpw1 (synCvv))) (synCvv)) p0010
      p0011
  have p0013 :=
    @gSifmap (synCpw1 (synCpw1 (synCvv))) (synCvv) (synCwppdirecth1famfn)
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCvv)))) (synCpw1 (synCvv))
      (synCsi (synCwppdirecth1famfn))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gFfn (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCpw1 (synCpw1 (synCvv))) (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gDffn2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0020 :=
    @gMpbi
      (synWfn (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0018 p0019
  have p0021 :=
    @gPm32i
      (synWfn (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCvv))
      (synWf (synCsi (synCsi (synCwppdirecth1famfn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))) (synCvv))
      p0009 p0020
  have p0022 :=
    @gFnfco (synCvv) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
      (synCsi (synCsi (synCwppdirecth1famfn)))
  have p0023 := Nominal.mp p0021 p0022
  have p0024 := (Nominal.classEqRefl (synCwppdirecth2famfn))
  have p0025 :=
    @gFneq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCwppdirecth2famfn)
      (synCcom (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
        (synCsi (synCsi (synCwppdirecth1famfn))))
      p0024
  have p0026 :=
    @gMpbir
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (synWfn (synCcom
          (synCcom (synCimage (synCwpplitphnordpointfn)) (synCwppfamilyrep2fn))
          (synCsi (synCsi (synCwppdirecth1famfn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0023 p0025
  have p0027 := @gSnex (synCsn (synCnc X))
  have p0028 := @gSnelpw1 (synCsn (synCsn (synCnc X))) (synCvv)
  have p0029 :=
    @gMpbir (.classMem (synCsn (synCsn (synCsn (synCnc X)))) (synCpw1 (synCvv)))
      (.classMem (synCsn (synCsn (synCnc X))) (synCvv)) p0027 p0028
  have p0030 := @gSnelpw1 (synCsn (synCsn (synCsn (synCnc X)))) (synCpw1 (synCvv))
  have p0031 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCnc X)))))
        (synCpw1 (synCpw1 (synCvv))))
      (.classMem (synCsn (synCsn (synCsn (synCnc X)))) (synCpw1 (synCvv))) p0029
      p0030
  have p0032 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (synCnc X)))))
      (synCpw1 (synCpw1 (synCvv)))
  have p0033 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
        (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCnc X)))))
        (synCpw1 (synCpw1 (synCvv))))
      p0031 p0032
  have p0034 :=
    @gSnelpw1 (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
      (synCpw1 (synCpw1 (synCpw1 (synCvv))))
  have p0035 :=
    @gMpbir
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
        (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      p0033 p0034
  have p0036 :=
    @gPm32i
      (synWfn (synCwppdirecth2famfn) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv))))))
      p0026 p0035
  have p0037 :=
    @gFvco2 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCvv)))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
      (synCimage (synCen)) (synCwppdirecth2famfn)
  have p0038 := Nominal.mp p0036 p0037
  have p0044 :=
    @gWppdirecth2famfnvalndv (synCsn (synCsn (synCsn (synCsn (synCnc X))))) p0031
  have p0045 :=
    @gFveq2i
      (synCfv (synCwppdirecth2famfn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1 (synCfv (synCwppdirecth1famfn)
              (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))))
      (synCimage (synCen)) p0044
  have p0046 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synCfv (synCimage (synCen)) (synCfv (synCwppdirecth2famfn)
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))))
      (synCfv (synCimage (synCen)) (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1
              (synCfv (synCwppdirecth1famfn)
                (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))))
      p0038 p0045
  have p0048 := @gWppdirecth1famfnvalndv (synCsn (synCsn (synCnc X))) p0027
  have p0049 := @gNcex X
  have p0050 := @gWppdirecte2famfnvalndv (synCnc X) p0049
  have p0052 := @gWpppowset2imexndv (synCnc X) p0049
  have p0053 :=
    @gEqeltri (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X))))
      (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 (synCnc X)))) (synCvv) p0050
      p0052
  have p0054 :=
    @gWpplitphnordimexndv
      (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))) p0053
  have p0055 :=
    @gEqeltri
      (synCfv (synCwppdirecth1famfn) (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
      (synCima (synCwpplitphnordpointfn) (synCpw1
          (synCpw1 (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))))))
      (synCvv) p0048 p0054
  have p0062 := @gEnrflx X hyp_wppconcrete6codefnvalndv_1
  have p0063 := @gElnc X X
  have p0064 := @gMpbir (.classMem X (synCnc X)) (synWbr X (synCen) X) p0062 p0063
  have p0065 := @gWpppowset2imcanndv X (synCnc X) p0049 p0064
  have p0068 :=
    @gEleq2i (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X))))
      (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 (synCnc X))))
      (synCpw (synCpw X)) p0050
  have p0069 :=
    @gMpbir
      (.classMem (synCpw (synCpw X))
        (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))))
      (.classMem (synCpw (synCpw X))
        (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 (synCnc X)))))
      p0065 p0068
  have p0070 :=
    @gWpplitphnordimcanndv (synCpw (synCpw X))
      (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))) p0053 p0069
  have p0073 :=
    @gEleq2i
      (synCfv (synCwppdirecth1famfn) (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
      (synCima (synCwpplitphnordpointfn) (synCpw1
          (synCpw1 (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))))))
      (synChnord (synCpw (synCpw X))) p0048
  have p0074 :=
    @gMpbir
      (.classMem (synChnord (synCpw (synCpw X))) (synCfv (synCwppdirecth1famfn)
          (synCsn (synCsn (synCsn (synCsn (synCnc X)))))))
      (.classMem (synChnord (synCpw (synCpw X))) (synCima (synCwpplitphnordpointfn)
          (synCpw1 (synCpw1
              (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X))))))))
      p0070 p0073
  have p0085 := @gSsid (synCnc X)
  have p0086 := @gWpppowset2imssndv X (synCnc X) p0049 p0085
  have p0087 :=
    @gEqsstri (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X))))
      (synCima (synCwpppowset2fn) (synCpw1 (synCpw1 (synCnc X))))
      (synCnc (synCpw (synCpw X))) p0050 p0086
  have p0088 :=
    @gWpplitphnordimssndv (synCpw (synCpw X))
      (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))) p0053 p0087
  have p0089 :=
    @gEqsstri
      (synCfv (synCwppdirecth1famfn) (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
      (synCima (synCwpplitphnordpointfn) (synCpw1
          (synCpw1 (synCfv (synCwppdirecte2famfn) (synCsn (synCsn (synCnc X)))))))
      (synCnc (synChnord (synCpw (synCpw X)))) p0048 p0088
  have p0090 :=
    @gWpplitphnordcardvalndv (synChnord (synCpw (synCpw X)))
      (synCfv (synCwppdirecth1famfn) (synCsn (synCsn (synCsn (synCsn (synCnc X))))))
      p0055 p0074 p0089
  have p0091 :=
    @gEqtri
      (synCfv (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synCfv (synCimage (synCen)) (synCima (synCwpplitphnordpointfn) (synCpw1 (synCpw1
              (synCfv (synCwppdirecth1famfn)
                (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))))
      (synChncard (synChnord (synCpw (synCpw X)))) p0046 p0090
  have p0092 :=
    @gEqtri
      (synCfv (synCwppconcrete6codefn)
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synCfv (synCcom (synCimage (synCen)) (synCwppdirecth2famfn))
        (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCnc X))))))))
      (synChncard (synChnord (synCpw (synCpw X)))) p0001 p0091
  exact p0092

/-- Checked nominal proof certificate identified upstream as `g_wppcardt6fnmapndv`. -/
@[expose]
noncomputable def gWppcardt6fnmapndv :
    Nominal.NPrf
      (synWf (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCncs)) :=
  by
  have p0000 := @gWppcardt2fnmapndv
  have p0001 := @gWppcardt4fnmapndv
  have p0002 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))) (synCncs)
      (synCwppcardt4fn)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gSifmap (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))
      (synCpw1 (synCncs)) (synCsi (synCwppcardt4fn))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i (synWf (synCwppcardt2fn) (synCpw1 (synCpw1 (synCncs))) (synCncs))
      (synWf (synCsi (synCsi (synCwppcardt4fn)))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
        (synCpw1 (synCpw1 (synCncs))))
      p0000 p0005
  have p0007 :=
    @gFco (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCpw1 (synCpw1 (synCncs))) (synCncs) (synCwppcardt2fn)
      (synCsi (synCsi (synCwppcardt4fn)))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := (Nominal.classEqRefl (synCwppcardt6fn))
  have p0010 :=
    @gFeq1i (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs)))))))
      (synCncs) (synCwppcardt6fn)
      (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn)))) p0009
  have p0011 :=
    @gMpbir
      (synWf (synCwppcardt6fn)
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      (synWf (synCcom (synCwppcardt2fn) (synCsi (synCsi (synCwppcardt4fn))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCncs))))))) (synCncs))
      p0008 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end
