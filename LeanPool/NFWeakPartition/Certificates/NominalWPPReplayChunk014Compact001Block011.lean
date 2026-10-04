/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassordcl`. -/
@[expose]
noncomputable def gHnwcutclassordcl (B : Class) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassordcl_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D)
        (.classMem (synCec (synChnwcutcode R D B) (synChwniso D)) (synChnord D))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.imp (.classMem B D) (.classMem (synCec (synChnwcutcode R D B) (synChwniso D))
            (synChnord D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @gElex B D
  have p0001 := @gEleq1 (.cv x) B D
  have p0002 := @gHnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @gEceq1 (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B) (synChwniso D)
  have p0004 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D B) (synChwniso D)))
      p0002 p0003
  have p0005 :=
    @gEleq1d (.classEq (.cv x) B) (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
      (synCec (synChnwcutcode R D B) (synChwniso D)) (synChnord D) p0004
  have p0006 :=
    @gImbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)) (synChnord D))
      (.classMem (synCec (synChnwcutcode R D B) (synChwniso D)) (synChnord D)) p0001
      p0005
  have p0007 := @gHnwcutclassord x D R dv_cache_0002 hyp_hnwcutclassordcl_1
  have p0008 :=
    @gVtoclg
      (.imp (.classMem (.cv x) D)
        (.classMem (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)) (synChnord D)))
      (.imp (.classMem B D)
        (.classMem (synCec (synChnwcutcode R D B) (synChwniso D)) (synChnord D)))
      x B (synCvv) dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B D)
      (.classMem (synCec (synChnwcutcode R D B) (synChwniso D)) (synChnord D)) p0000
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmapf`. -/
@[expose]
noncomputable def gHnwcutmapf (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapf_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWf (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_D, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0003 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0004 : p ∉ ((synCpw1 (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0005 : p ∉ ((synChnord D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_p_not_D, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfHnwcutmap D R p
      dv_cache_0001 dv_cache_0002
  have p0001 := @gPw12argcl (.cv p) D
  have p0002 :=
    @gSimpld (.classMem (.cv p) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv p))) D)
      (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))) p0001
  have p0003 :=
    @gHnwcutclassordcl (synCuni (synCuni (.cv p))) D R dv_cache_0003 hyp_hnwcutmapf_1
  have p0004 :=
    @gSyl (.classMem (.cv p) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv p))) D)
      (.classMem (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D))
        (synChnord D))
      p0002 p0003
  have p0005 :=
    @gFmpti p (synCpw1 (synCpw1 D)) (synChnord D)
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D))
      (synChnwcutmap R D) dv_cache_0004 dv_cache_0005 p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmapval`. -/
@[expose]
noncomputable def gHnwcutmapval (D : Class) (R : Class) (q : Var)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapval_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ ({ q } : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : p ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_D, not_false_eq_true])
  have dv_cache_0002 : p ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0003 : Disjoint ((synCuni (synCuni (.cv p)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint ((synCuni (synCuni (.cv p)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((synCuni (.cv p))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv p)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ p } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show p ∉ (R).fv from (by exact fresh_p_not_R))))))))))
  have dv_cache_0004 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0005 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0006 :
    p ∉
      ((synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, fresh_p_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 : p ∉ ((synCpw1 (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_p_not_D,
          not_false_eq_true])
  have dv_cache_0008 : p ∉ ((Wff.classMem (.cv q) (synCpw1 (synCpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_D, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfHnwcutmap D R p
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gA1i
      (.classEq (synChnwcutmap R D) (synCmpt p (synCpw1 (synCpw1 D))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0000
  have p0002 := @gUnieq (.cv p) (.cv q)
  have p0003 :=
    @gUnieqd (.classEq (.cv p) (.cv q)) (synCuni (.cv p)) (synCuni (.cv q)) p0002
  have p0004 :=
    @gHnwcutcodeeq3 (synCuni (synCuni (.cv p))) (synCuni (synCuni (.cv q))) D R
      dv_cache_0003
  have p0005 :=
    @gSyl (.classEq (.cv p) (.cv q))
      (.classEq (synCuni (synCuni (.cv p))) (synCuni (synCuni (.cv q))))
      (.classEq (synChnwcutcode R D (synCuni (synCuni (.cv p))))
        (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      p0003 p0004
  have p0006 :=
    @gEceq1 (synChnwcutcode R D (synCuni (synCuni (.cv p))))
      (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)
  have p0007 :=
    @gSyl (.classEq (.cv p) (.cv q))
      (.classEq (synChnwcutcode R D (synCuni (synCuni (.cv p))))
        (synChnwcutcode R D (synCuni (synCuni (.cv q)))))
      (.classEq (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)))
      p0005 p0006
  have p0008 :=
    @gAdantl (.classEq (.cv p) (.cv q))
      (.classEq (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0007
  have p0009 := @gId (.classMem (.cv q) (synCpw1 (synCpw1 D)))
  have p0010 := @gPw12argcl (.cv q) D
  have p0011 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0010
  have p0012 :=
    @gHnwcutclassordcl (synCuni (synCuni (.cv q))) D R dv_cache_0004 hyp_hnwcutmapval_1
  have p0013 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
        (synChnord D))
      p0011 p0012
  have p0014 :=
    @gElex (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
      (synChnord D)
  have p0015 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
        (synChnord D))
      (.classMem (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
        (synCvv))
      p0013 p0014
  have p0016 :=
    @gFvmptd (.classMem (.cv q) (synCpw1 (synCpw1 D))) p (.cv q)
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv p)))) (synChwniso D))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
      (synCpw1 (synCpw1 D)) (synChnwcutmap R D) (synCvv) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0001 p0008 p0009 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeltnoiso`. -/
@[expose]
noncomputable def gHnwcutcodeltnoiso (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (.neg
          (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D)
            (synChnwcutcode R D (.cv y))))) :=
  by
  have p0000 := @gStrictseghwnisono x y D R
  have p0001 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0002 :=
    @gBreq1 (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synChnwcutcode R D (.cv y)) (synChwniso D)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := (Nominal.classEqRefl (synChnwcutcode R D (.cv y)))
  have p0005 :=
    @gBreq2 (synChnwcutcode R D (.cv y))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synChwniso D)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gBitri
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synChnwcutcode R D (.cv y)))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0003 p0006
  have p0008 :=
    @gBiimpi
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0007
  have p0009 :=
    @gA1i
      (.imp (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D)
          (synChnwcutcode R D (.cv y))) (synWbr (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synChwniso D) (synCop (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0008
  have p0010 :=
    @gMtod
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      (synWbr (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synChwniso D) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hwnisoclasseqbcl`. -/
@[expose]
noncomputable def gHwnisoclasseqbcl (A : Class) (B : Class) (C : Class)
    (hyp_hwnisoclasseqbcl_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
          (synWbr B (synChwniso A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0002 : v ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_B, not_false_eq_true])
  have dv_cache_0003 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0004 :
    v ∉
      ((Wff.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
          (synWb (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
            (synWbr B (synChwniso A) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_A, fresh_v_not_C, or_false, not_false_eq_true])
  have dv_cache_0005 :
    u ∉
      ((Wff.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWb (.classEq (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)))
            (synWbr B (synChwniso A) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_not_A, fresh_u_ne_v, or_false,
          not_false_eq_true])
  have p0000 := @gSimpl (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0001 := @gElex B (synChwcn A)
  have p0002 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synChwcn A)) (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpr (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0004 := @gElex C (synChwcn A)
  have p0005 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A)) (.classMem C (synCvv)) p0003 p0004
  have p0006 :=
    @gJca (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synCvv)) (.classMem C (synCvv)) p0002 p0005
  have p0007 := @gEleq1 (.cv u) B (synChwcn A)
  have p0008 := @gBiid (.classMem (.cv v) (synChwcn A))
  have p0009 :=
    @gA1i (synWb (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classEq (.cv u) B) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv v) (synChwcn A)) p0007 p0009
  have p0011 := @gEceq1 (.cv u) B (synChwniso A)
  have p0012 :=
    @gEqeq1d (.classEq (.cv u) B) (synCec (.cv u) (synChwniso A))
      (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)) p0011
  have p0013 := @gBreq1 (.cv u) B (.cv v) (synChwniso A)
  have p0014 :=
    @gBibi12d (.classEq (.cv u) B)
      (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
      (.classEq (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr B (synChwniso A) (.cv v)) p0012
      p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv u) B)
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWb (.classEq (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)))
        (synWbr B (synChwniso A) (.cv v)))
      p0010 p0014
  have p0016 := @gBiid (.classMem B (synChwcn A))
  have p0017 :=
    @gA1i (synWb (.classMem B (synChwcn A)) (.classMem B (synChwcn A)))
      (.classEq (.cv v) C) p0016
  have p0018 := @gEleq1 (.cv v) C (synChwcn A)
  have p0019 :=
    @gAnbi12d (.classEq (.cv v) C) (.classMem B (synChwcn A))
      (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A))
      (.classMem C (synChwcn A)) p0017 p0018
  have p0020 := @gEceq1 (.cv v) C (synChwniso A)
  have p0021 :=
    @gEqeq2d (.classEq (.cv v) C) (synCec (.cv v) (synChwniso A))
      (synCec C (synChwniso A)) (synCec B (synChwniso A)) p0020
  have p0022 := @gBreq2 (.cv v) C B (synChwniso A)
  have p0023 :=
    @gBibi12d (.classEq (.cv v) C)
      (.classEq (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)))
      (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
      (synWbr B (synChwniso A) (.cv v)) (synWbr B (synChwniso A) C) p0021 p0022
  have p0024 :=
    @gImbi12d (.classEq (.cv v) C)
      (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWb (.classEq (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)))
        (synWbr B (synChwniso A) (.cv v)))
      (synWb (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
        (synWbr B (synChwniso A) C))
      p0019 p0023
  have p0025 :=
    @gA1i (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      hyp_hwnisoclasseqbcl_1
  have p0026 :=
    @gId (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0027 :=
    @gJca (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0025
      p0026
  have p0028 := @gHwnisoclasseqb v u A
  have p0029 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWb (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      p0027 p0028
  have p0030 :=
    @gVtocl2g
      (.imp (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) (synWb
          (.classEq (synCec (.cv u) (synChwniso A)) (synCec (.cv v) (synChwniso A)))
          (synWbr (.cv u) (synChwniso A) (.cv v))))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWb (.classEq (synCec B (synChwniso A)) (synCec (.cv v) (synChwniso A)))
          (synWbr B (synChwniso A) (.cv v))))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
          (synWbr B (synChwniso A) C)))
      u v B C (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0015 p0024 p0029
  have p0031 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
          (synWbr B (synChwniso A) C)))
      p0006 p0030
  have p0032 :=
    @gPm243i (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (synWb (.classEq (synCec B (synChwniso A)) (synCec C (synChwniso A)))
        (synWbr B (synChwniso A) C))
      p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodecncl`. -/
@[expose]
noncomputable def gHnwcutcodecncl (B : Class) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutcodecncl_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (.classMem B D) (.classMem (synChnwcutcode R D B) (synChwcn D))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((Wff.imp (.classMem B D) (.classMem (synChnwcutcode R D B) (synChwcn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 := @gElex B D
  have p0001 := @gEleq1 (.cv x) B D
  have p0002 := @gHnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0003 :=
    @gEleq1d (.classEq (.cv x) B) (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B)
      (synChwcn D) p0002
  have p0004 :=
    @gImbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synChnwcutcode R D B) (synChwcn D)) p0001 p0003
  have p0005 := @gHnwcutcodecn x D R dv_cache_0002 hyp_hnwcutcodecncl_1
  have p0006 :=
    @gVtoclg
      (.imp (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D)))
      (.imp (.classMem B D) (.classMem (synChnwcutcode R D B) (synChwcn D))) x B
      (synCvv) dv_cache_0003 dv_cache_0004 p0004 p0005
  have p0007 :=
    @gMpcom (.classMem B (synCvv)) (.classMem B D)
      (.classMem (synChnwcutcode R D B) (synChwcn D)) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassltne`. -/
@[expose]
noncomputable def gHnwcutclassltne (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassltne_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) D) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (.neg
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      hyp_hnwcutclassltne_1
  have p0001 :=
    @gSimpl (.classMem (.cv y) D)
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0002 :=
    @gJca
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr R (synCwe) D) (.classMem (.cv y) D) p0000 p0001
  have p0003 :=
    @gSimpr (.classMem (.cv y) D)
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0004 :=
    @gJca
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0002 p0003
  have p0005 := @gHnwcutcodeltnoiso x y D R
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D)
          (synChnwcutcode R D (.cv y))))
      p0004 p0005
  have p0008 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))
  have p0009 :=
    @gSsel (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) D
      (.cv x)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv x) D) p0003 p0010
  have p0012 := @gHnwcutcodecncl (.cv x) D R dv_cache_0001 hyp_hnwcutclassltne_1
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv x) D) (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D)) p0011
      p0012
  have p0015 := @gHnwcutcodecncl (.cv y) D R dv_cache_0001 hyp_hnwcutclassltne_1
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) D) (.classMem (synChnwcutcode R D (.cv y)) (synChwcn D)) p0001
      p0015
  have p0017 :=
    @gJca
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
      (.classMem (synChnwcutcode R D (.cv y)) (synChwcn D)) p0013 p0016
  have p0018 := @gBrex R D (synCwe)
  have p0019 := @gSimpr (.classMem R (synCvv)) (.classMem D (synCvv))
  have p0020 :=
    @gSyl (synWbr R (synCwe) D)
      (synWa (.classMem R (synCvv)) (.classMem D (synCvv))) (.classMem D (synCvv))
      p0018 p0019
  have p0021 := Nominal.mp hyp_hnwcutclassltne_1 p0020
  have p0022 :=
    @gHwnisoclasseqbcl D (synChnwcutcode R D (.cv x)) (synChnwcutcode R D (.cv y))
      p0021
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (.classMem (synChnwcutcode R D (.cv x)) (synChwcn D))
        (.classMem (synChnwcutcode R D (.cv y)) (synChwcn D)))
      (synWb (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
        (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y))))
      p0017 p0022
  have p0024 :=
    @gBiimpd
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      p0023
  have p0025 :=
    @gCon3d
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D) (synChnwcutcode R D (.cv y)))
      p0024
  have p0026 :=
    @gMpd
      (synWa (.classMem (.cv y) D) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.neg (synWbr (synChnwcutcode R D (.cv x)) (synChwniso D)
          (synChnwcutcode R D (.cv y))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0006 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassinj`. -/
@[expose]
noncomputable def gHnwcutclassinj (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassinj_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
          (.classEq (.cv x) (.cv y)))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWne (.cv x) (.cv y))
  have p0001 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      p0000 p0001
  have p0003 := @gWppweconnex D R
  have p0004 := Nominal.mp hyp_hnwcutclassinj_1 p0003
  have p0005 :=
    @gA1i (synWbr R (synCconnex) D)
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      p0004
  have p0007 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
  have p0008 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0007
      p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classMem (.cv x) D) p0000 p0009
  have p0013 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0007
      p0013
  have p0015 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classMem (.cv y) D) p0000 p0014
  have p0016 :=
    @gConnexd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      D R (.cv x) (.cv y) p0005 p0010 p0015
  have p0017 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) D) p0017 p0010
  have p0024 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0026 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWne (.cv x) (.cv y))
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWne (.cv x) (.cv y)) p0017 p0026
  have p0028 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)) p0024 p0027
  have p0029 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)))
      p0023 p0028
  have p0030 := @gElstrictseg y x D R
  have p0031 :=
    @gBiimpri
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0029 p0031
  have p0033 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0032
  have p0034 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv y) D) p0034 p0015
  have p0041 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
  have p0044 :=
    @gNecomd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.cv x) (.cv y) p0026
  have p0045 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWne (.cv y) (.cv x)) p0034 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)) p0041 p0045
  have p0047 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
      p0040 p0046
  have p0048 := @gElstrictseg x y D R
  have p0049 :=
    @gBiimpri
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0048
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
            (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
          (synWne (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0047 p0049
  have p0051 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0050
  have p0052 :=
    @gOrim12d
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWbr (.cv x) R (.cv y))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0033 p0051
  have p0053 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWo (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0016 p0052
  have p0059 := @gHnwcutclassltne x y D R dv_cache_0001 hyp_hnwcutclassinj_1
  have p0060 :=
    @gEx (.classMem (.cv y) D)
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0059
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv y) D)
      (.imp (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))) (.neg
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))))
      p0015 p0060
  have p0067 := @gHnwcutclassltne y x D R dv_cache_0001 hyp_hnwcutclassinj_1
  have p0068 :=
    @gEx (.classMem (.cv x) D)
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))))
      p0067
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x) D)
      (.imp (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (.neg
          (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)))))
      p0010 p0068
  have p0070 :=
    @gEqcom (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
      (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
  have p0071 :=
    @gBiimpi
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)))
      p0070
  have p0072 :=
    @gCon3i
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv x)) (synChwniso D)))
      p0071
  have p0073 :=
    @gSyl6
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0069 p0072
  have p0074 :=
    @gJaod
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0061 p0073
  have p0075 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (synWo (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      p0053 p0074
  have p0076 :=
    @gPm221dd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))) (synWne (.cv x) (.cv y)))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.neg (synWne (.cv x) (.cv y))) p0002 p0075
  have p0077 :=
    @gPm201da
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (synWne (.cv x) (.cv y)) p0076
  have p0078 := @gNne (.cv x) (.cv y)
  have p0079 :=
    @gSylib
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))))
      (.neg (synWne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0077 p0078
  have p0080 :=
    @gEx (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (.cv x) (.cv y)) p0079
  exact p0080

/-- Checked nominal proof certificate identified upstream as `g_hnwcutclassinjcl`. -/
@[expose]
noncomputable def gHnwcutclassinjcl (B : Class) (C : Class) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutclassinjcl_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact
      (show Disjoint ((Class.cv x)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ x } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0003 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
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
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.imp (synWa (.classMem B D) (.classMem C D)) (.imp
            (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
              (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((Wff.imp (synWa (.classMem B D) (.classMem (.cv y) D)) (.imp
            (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
              (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
            (.classEq B (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_R,
          or_false, not_false_eq_true])
  have p0000 := @gSimpl (.classMem B D) (.classMem C D)
  have p0001 := @gElex B D
  have p0002 :=
    @gSyl (synWa (.classMem B D) (.classMem C D)) (.classMem B D)
      (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpr (.classMem B D) (.classMem C D)
  have p0004 := @gElex C D
  have p0005 :=
    @gSyl (synWa (.classMem B D) (.classMem C D)) (.classMem C D)
      (.classMem C (synCvv)) p0003 p0004
  have p0006 :=
    @gJca (synWa (.classMem B D) (.classMem C D)) (.classMem B (synCvv))
      (.classMem C (synCvv)) p0002 p0005
  have p0007 := @gEleq1 (.cv x) B D
  have p0008 := @gBiid (.classMem (.cv y) D)
  have p0009 :=
    @gA1i (synWb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D)
      (.classMem (.cv y) D) (.classMem (.cv y) D) p0007 p0009
  have p0011 := @gHnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0012 :=
    @gEceq1 (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B) (synChwniso D)
  have p0013 :=
    @gSyl (.classEq (.cv x) B)
      (.classEq (synChnwcutcode R D (.cv x)) (synChnwcutcode R D B))
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D B) (synChwniso D)))
      p0011 p0012
  have p0014 :=
    @gEqeq1d (.classEq (.cv x) B) (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
      (synCec (synChnwcutcode R D B) (synChwniso D))
      (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)) p0013
  have p0015 := @gId (.classEq (.cv x) B)
  have p0016 := @gEqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0015
  have p0017 :=
    @gImbi12d (.classEq (.cv x) B)
      (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0014 p0016
  have p0018 :=
    @gImbi12d (.classEq (.cv x) B) (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem B D) (.classMem (.cv y) D))
      (.imp (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq (.cv x) (.cv y)))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq B (.cv y)))
      p0010 p0017
  have p0019 := @gBiid (.classMem B D)
  have p0020 := @gA1i (synWb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0019
  have p0021 := @gEleq1 (.cv y) C D
  have p0022 :=
    @gAnbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D)
      (.classMem C D) p0020 p0021
  have p0023 := @gHnwcutcodeeq3 (.cv y) C D R dv_cache_0002
  have p0024 :=
    @gEceq1 (synChnwcutcode R D (.cv y)) (synChnwcutcode R D C) (synChwniso D)
  have p0025 :=
    @gSyl (.classEq (.cv y) C)
      (.classEq (synChnwcutcode R D (.cv y)) (synChnwcutcode R D C))
      (.classEq (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      p0023 p0024
  have p0026 :=
    @gEqeq2d (.classEq (.cv y) C) (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))
      (synCec (synChnwcutcode R D C) (synChwniso D))
      (synCec (synChnwcutcode R D B) (synChwniso D)) p0025
  have p0027 := @gId (.classEq (.cv y) C)
  have p0028 := @gEqeq2d (.classEq (.cv y) C) (.cv y) C B p0027
  have p0029 :=
    @gImbi12d (.classEq (.cv y) C)
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
      (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
        (synCec (synChnwcutcode R D C) (synChwniso D)))
      (.classEq B (.cv y)) (.classEq B C) p0026 p0028
  have p0030 :=
    @gImbi12d (.classEq (.cv y) C) (synWa (.classMem B D) (.classMem (.cv y) D))
      (synWa (.classMem B D) (.classMem C D))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq B (.cv y)))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))
      p0022 p0029
  have p0031 := @gHnwcutclassinj x y D R dv_cache_0003 hyp_hnwcutclassinjcl_1
  have p0032 :=
    @gVtocl2g
      (.imp (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp
          (.classEq (synCec (synChnwcutcode R D (.cv x)) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D)))
          (.classEq (.cv x) (.cv y))))
      (.imp (synWa (.classMem B D) (.classMem (.cv y) D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D (.cv y)) (synChwniso D))) (.classEq B (.cv y))))
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C)))
      x y B C (synCvv) (synCvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 p0018 p0030 p0031
  have p0033 :=
    @gSyl (synWa (.classMem B D) (.classMem C D))
      (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.imp (synWa (.classMem B D) (.classMem C D)) (.imp
          (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
            (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C)))
      p0006 p0032
  have p0034 :=
    @gPm243i (synWa (.classMem B D) (.classMem C D))
      (.imp (.classEq (synCec (synChnwcutcode R D B) (synChwniso D))
          (synCec (synChnwcutcode R D C) (synChwniso D))) (.classEq B C))
      p0033
  exact p0034


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hnwcutmapf1`. -/
@[expose]
noncomputable def gHnwcutmapf1 (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv)
    (hyp_hnwcutmapf1_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf (synWf1 (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : r ∉ ((synCpw1 (synCpw1 D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_r_not_D,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synWbr R (synCwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_q_not_R, fresh_q_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((synWbr R (synCwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0006 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_q_not_D,
          not_false_eq_true])
  have dv_cache_0007 : q ∉ ((synChnwcutmap R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          Finset.mem_union, fresh_q_not_D, fresh_q_not_R, or_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((synChnwcutmap R D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap,
          Finset.mem_union, fresh_r_not_D, fresh_r_not_R, or_false, not_false_eq_true])
  have p0000 := @gHnwcutmapf D R dv_cache_0001 hyp_hnwcutmapf1_1
  have p0001 :=
    @gSimpl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synChnwcutmap R D) (.cv q)) (synCfv (synChnwcutmap R D) (.cv r)))
  have p0002 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (.cv r) (synCpw1 (synCpw1 D))))
  have p0003 :=
    @gSimpl (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
  have p0004 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (.cv r) (synCpw1 (synCpw1 D))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D))) p0002 p0003
  have p0005 := @gPw12argcl (.cv q) D
  have p0006 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv q))) D)
        (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))))
      p0004 p0005
  have p0007 :=
    @gSimprd
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0008 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0001 p0007
  have p0013 := @gHnwcutmapval D R q dv_cache_0001 hyp_hnwcutmapf1_1
  have p0014 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classEq (synCfv (synChnwcutmap R D) (.cv q))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)))
      p0004 p0013
  have p0015 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synChnwcutmap R D) (.cv q))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)))
      p0001 p0014
  have p0016 :=
    @gEqcomd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synCfv (synChnwcutmap R D) (.cv q))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D)) p0015
  have p0017 :=
    @gSimpr
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synChnwcutmap R D) (.cv q)) (synCfv (synChnwcutmap R D) (.cv r)))
  have p0018 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
      (synCfv (synChnwcutmap R D) (.cv q)) (synCfv (synChnwcutmap R D) (.cv r)) p0016
      p0017
  have p0021 :=
    @gSimpr (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
  have p0022 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
        (.classMem (.cv r) (synCpw1 (synCpw1 D))))
      (.classMem (.cv r) (synCpw1 (synCpw1 D))) p0002 p0021
  have p0023 := @gHnwcutmapval D R r dv_cache_0001 hyp_hnwcutmapf1_1
  have p0024 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
      (.classEq (synCfv (synChnwcutmap R D) (.cv r))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso D)))
      p0022 p0023
  have p0025 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synChnwcutmap R D) (.cv r))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso D)))
      p0001 p0024
  have p0026 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
      (synCfv (synChnwcutmap R D) (.cv r))
      (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso D)) p0018
      p0025
  have p0033 :=
    @gSimpld
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classEq (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))) p0006
  have p0034 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv q))) D) p0001 p0033
  have p0039 := @gPw12argcl (.cv r) D
  have p0040 :=
    @gSyl
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (.cv r) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv r))) D)
        (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))))
      p0022 p0039
  have p0041 :=
    @gSimpld
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv r))) D)
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0040
  have p0042 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv r))) D) p0001 p0041
  have p0043 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (.classMem (synCuni (synCuni (.cv q))) D)
      (.classMem (synCuni (synCuni (.cv r))) D) p0034 p0042
  have p0044 :=
    @gHnwcutclassinjcl (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r))) D R
      dv_cache_0001 hyp_hnwcutmapf1_1
  have p0045 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (.classMem (synCuni (synCuni (.cv q))) D)
        (.classMem (synCuni (synCuni (.cv r))) D))
      (.imp (.classEq
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
          (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso D)))
        (.classEq (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r)))))
      p0043 p0044
  have p0046 :=
    @gMpd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (.classEq (synCec (synChnwcutcode R D (synCuni (synCuni (.cv q)))) (synChwniso D))
        (synCec (synChnwcutcode R D (synCuni (synCuni (.cv r)))) (synChwniso D)))
      (.classEq (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r)))) p0026 p0045
  have p0047 :=
    @gSneqd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synCuni (synCuni (.cv q))) (synCuni (synCuni (.cv r))) p0046
  have p0048 :=
    @gSneqd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCsn (synCuni (synCuni (.cv r))))
      p0047
  have p0049 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv q)))))
      (synCsn (synCsn (synCuni (synCuni (.cv r))))) p0008 p0048
  have p0056 :=
    @gSimprd
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classMem (synCuni (synCuni (.cv r))) D)
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0040
  have p0057 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r)))))) p0001 p0056
  have p0058 :=
    @gEqcomd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (.cv r) (synCsn (synCsn (synCuni (synCuni (.cv r))))) p0057
  have p0059 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
            (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
        (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))))
      (.cv q) (synCsn (synCsn (synCuni (synCuni (.cv r))))) (.cv r) p0049 p0058
  have p0060 :=
    @gEx
      (synWa (synWbr R (synCwe) D) (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D)))
          (.classMem (.cv r) (synCpw1 (synCpw1 D)))))
      (.classEq (synCfv (synChnwcutmap R D) (.cv q)) (synCfv (synChnwcutmap R D) (.cv r)))
      (.classEq (.cv q) (.cv r)) p0059
  have p0061 :=
    @gRalrimivva (synWbr R (synCwe) D)
      (.imp (.classEq (synCfv (synChnwcutmap R D) (.cv q))
          (synCfv (synChnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r)))
      q r (synCpw1 (synCpw1 D)) (synCpw1 (synCpw1 D)) dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0060
  have p0062 := Nominal.mp hyp_hnwcutmapf1_1 p0061
  have p0063 :=
    @gPm32i (synWf (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D))
      (synWral q (synCpw1 (synCpw1 D)) (synWral r (synCpw1 (synCpw1 D)) (.imp
            (.classEq (synCfv (synChnwcutmap R D) (.cv q))
              (synCfv (synChnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r)))))
      p0000 p0062
  have p0064 :=
    @gDff13 q r (synCpw1 (synCpw1 D)) (synChnord D) (synChnwcutmap R D) dv_cache_0006
      dv_cache_0002 dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0065_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D))
        (synWa (synWf (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D))
          (synWral q (synCpw1 (synCpw1 D)) (synWral r (synCpw1 (synCpw1 D)) (.imp
                (.classEq (synCfv (synChnwcutmap R D) (.cv q))
                  (synCfv (synChnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synChnwcutmap synCmpt
          synCpw1 synCec synCima synWrex synWbr synCop synCun synCsn
          synChnwcutcode synCuni synChwniso synChnord synCqs synChwcn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0064
  have p0065 :=
    @gMpbir (synWf1 (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D))
      (synWa (synWf (synChnwcutmap R D) (synCpw1 (synCpw1 D)) (synChnord D))
        (synWral q (synCpw1 (synCpw1 D)) (synWral r (synCpw1 (synCpw1 D)) (.imp
              (.classEq (synCfv (synChnwcutmap R D) (.cv q))
                (synCfv (synChnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))))))
      p0063 p0065_e01_recanon
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1exg`. -/
@[expose]
noncomputable def gHnqmap1exg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCvv)) (.classMem (synChnqmap1 A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnqmap1 A))
  have p0001 := @gHwnisoexg A
  have p0002 := @gImageexg (synChwniso A) (synCvv)
  have p0003 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChwniso A) (synCvv))
      (.classMem (synCimage (synChwniso A)) (synCvv)) p0001 p0002
  have p0004 := @gHwcnexg A
  have p0005 := @gPw1exg (synChwcn A) (synCvv)
  have p0006 :=
    @gSyl (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))
      (.classMem (synCpw1 (synChwcn A)) (synCvv)) p0004 p0005
  have p0007 :=
    @gJca (.classMem A (synCvv)) (.classMem (synCimage (synChwniso A)) (synCvv))
      (.classMem (synCpw1 (synChwcn A)) (synCvv)) p0003 p0006
  have p0008 :=
    @gResexg (synCimage (synChwniso A)) (synCpw1 (synChwcn A)) (synCvv) (synCvv)
  have p0009 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synCimage (synChwniso A)) (synCvv))
        (.classMem (synCpw1 (synChwcn A)) (synCvv)))
      (.classMem (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A))) (synCvv))
      p0007 p0008
  have p0010 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChnqmap1 A)
      (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A))) (synCvv) p0000
      p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1fn`. -/
@[expose]
noncomputable def gHnqmap1fn (A : Class)
    (hyp_hnqmap1fn_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A))) :=
  by
  have p0000 := @gHwnisoexg A
  have p0001 := Nominal.mp hyp_hnqmap1fn_1 p0000
  have p0002 := @gWppimagefn (synChwniso A) p0001
  have p0003 := @gSsv (synCpw1 (synChwcn A))
  have p0004 :=
    @gPm32i (synWfn (synCimage (synChwniso A)) (synCvv))
      (synWss (synCpw1 (synChwcn A)) (synCvv)) p0002 p0003
  have p0005 := @gFnssres (synCvv) (synCpw1 (synChwcn A)) (synCimage (synChwniso A))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := (Nominal.classEqRefl (synChnqmap1 A))
  have p0008 :=
    @gFneq1i (synCpw1 (synChwcn A)) (synChnqmap1 A)
      (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A))) p0007
  have p0009 :=
    @gMpbir (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A)))
      (synWfn (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A)))
        (synCpw1 (synChwcn A)))
      p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1val`. -/
@[expose]
noncomputable def gHnqmap1val (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (hyp_hnqmap1val_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u)))
          (synCec (.cv u) (synChwniso A)))) :=
  by
  have dv_cache_0001 : Disjoint ((synCsn (.cv u))).fv ((synChwniso A)).fv := by
    exact
      (show Disjoint ((synCsn (.cv u))).fv ((synChwniso A)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso];
          exact
            (show Disjoint (((Class.cv u)).fv) ((A).fv) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ u } : Finset Var)) ((A).fv) from
                    (Finset.disjoint_singleton_left.mpr
                      (show u ∉ (A).fv from (by exact dv_A_u))))))))
  have p0000 := (Nominal.classEqRefl (synChnqmap1 A))
  have p0001 :=
    @gFveq1i (synCsn (.cv u)) (synChnqmap1 A)
      (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A))) p0000
  have p0002 := @gSnelpw1 (.cv u) (synChwcn A)
  have p0003 :=
    @gBiimpri (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0002
  have p0004 :=
    @gFvres (synCsn (.cv u)) (synCpw1 (synChwcn A)) (synCimage (synChwniso A))
  have p0005 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classEq (synCfv (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A)))
          (synCsn (.cv u))) (synCfv (synCimage (synChwniso A)) (synCsn (.cv u))))
      p0003 p0004
  have p0006 :=
    @gSyl5eq (.classMem (.cv u) (synChwcn A))
      (synCfv (synChnqmap1 A) (synCsn (.cv u)))
      (synCfv (synCres (synCimage (synChwniso A)) (synCpw1 (synChwcn A)))
        (synCsn (.cv u)))
      (synCfv (synCimage (synChwniso A)) (synCsn (.cv u))) p0001 p0005
  have p0007 := @gHwnisoexg A
  have p0008 := Nominal.mp hyp_hnqmap1val_1 p0007
  have p0009 := @gSnex (.cv u)
  have p0010 := @gWppfvimage (synCsn (.cv u)) (synChwniso A) dv_cache_0001 p0008 p0009
  have p0011 := (Nominal.classEqRefl (synCec (.cv u) (synChwniso A)))
  have p0012 :=
    @gEqtr4i (synCfv (synCimage (synChwniso A)) (synCsn (.cv u)))
      (synCima (synChwniso A) (synCsn (.cv u))) (synCec (.cv u) (synChwniso A)) p0010
      p0011
  have p0013 :=
    @gSyl6eq (.classMem (.cv u) (synChwcn A))
      (synCfv (synChnqmap1 A) (synCsn (.cv u)))
      (synCfv (synCimage (synChwniso A)) (synCsn (.cv u)))
      (synCec (.cv u) (synChwniso A)) p0006 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1f`. -/
@[expose]
noncomputable def gHnqmap1f (A : Class)
    (hyp_hnqmap1f_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ ((Class.cv q)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_q, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0004 :
    u ∉ ((Wff.classMem (synCfv (synChnqmap1 A) (.cv q)) (synChnord A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((synChnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((synChnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_q_not_A, not_false_eq_true])
  have p0000 := @gHnqmap1fn A hyp_hnqmap1f_1
  have p0002 := @gElpw1 u (.cv q) (synChwcn A) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv u)))
  have p0004 := @gFveq2 (.cv q) (synCsn (.cv u)) (synChnqmap1 A)
  have p0005 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv u))))
      (.classEq (.cv q) (synCsn (.cv u)))
      (.classEq (synCfv (synChnqmap1 A) (.cv q)) (synCfv (synChnqmap1 A) (synCsn (.cv u))))
      p0003 p0004
  have p0006 := @gHnqmap1val u A dv_cache_0003 hyp_hnqmap1f_1
  have p0007 := @gHwnisoclasselhnord u A dv_cache_0003 hyp_hnqmap1f_1
  have p0008 :=
    @gEqeltrd (.classMem (.cv u) (synChwcn A))
      (synCfv (synChnqmap1 A) (synCsn (.cv u))) (synCec (.cv u) (synChwniso A))
      (synChnord A) p0006 p0007
  have p0009 :=
    @gAdantr (.classMem (.cv u) (synChwcn A))
      (.classMem (synCfv (synChnqmap1 A) (synCsn (.cv u))) (synChnord A))
      (.classEq (.cv q) (synCsn (.cv u))) p0008
  have p0010 :=
    @gEqeltrd
      (synWa (.classMem (.cv u) (synChwcn A)) (.classEq (.cv q) (synCsn (.cv u))))
      (synCfv (synChnqmap1 A) (.cv q)) (synCfv (synChnqmap1 A) (synCsn (.cv u)))
      (synChnord A) p0005 p0009
  have p0011 :=
    @gRexlimiva (.classEq (.cv q) (synCsn (.cv u)))
      (.classMem (synCfv (synChnqmap1 A) (.cv q)) (synChnord A)) u (synChwcn A)
      dv_cache_0004 p0010
  have p0012 :=
    @gSylbi (.classMem (.cv q) (synCpw1 (synChwcn A)))
      (synWrex u (synChwcn A) (.classEq (.cv q) (synCsn (.cv u))))
      (.classMem (synCfv (synChnqmap1 A) (.cv q)) (synChnord A)) p0002 p0011
  have p0013 :=
    @gRgen (.classMem (synCfv (synChnqmap1 A) (.cv q)) (synChnord A)) q
      (synCpw1 (synChwcn A)) p0012
  have p0014 :=
    @gPm32i (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A)))
      (synWral q (synCpw1 (synChwcn A))
        (.classMem (synCfv (synChnqmap1 A) (.cv q)) (synChnord A)))
      p0000 p0013
  have p0015 :=
    @gFnfvrnss q (synCpw1 (synChwcn A)) (synChnord A) (synChnqmap1 A) dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gPm32i (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A)))
      (synWss (synCrn (synChnqmap1 A)) (synChnord A)) p0000 p0016
  have p0018 :=
    (Nominal.biimpRefl (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A)))
  have p0019 :=
    @gMpbir (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
      (synWa (synWfn (synChnqmap1 A) (synCpw1 (synChwcn A)))
        (synWss (synCrn (synChnqmap1 A)) (synChnord A)))
      p0017 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_hnqmap1rn`. -/
@[expose]
noncomputable def gHnqmap1rn (A : Class)
    (hyp_hnqmap1rn_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCrn (synChnqmap1 A)) (synChnord A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_q_ne_u : q ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_q : u ≠ q := Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ ((synChwcn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_z, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0004 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synCsn (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_u,
          not_false_eq_true])
  have dv_cache_0006 : q ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0007 :
    q ∉ ((Wff.classEq (.cv z) (synCfv (synChnqmap1 A) (synCsn (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_u, fresh_q_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    u ∉
      ((synWrex q (synCpw1 (synChwcn A))
          (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_A, fresh_u_ne_z,
          fresh_u_ne_q, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCpw1 (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0010 : q ∉ ((synChnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((synChnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_z_not_A, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((synChnqmap1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_q_not_A, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((synChnqmap1 A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          fresh_z_not_A, not_false_eq_true])
  have dv_cache_0014 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have p0000 := @gHnqmap1f A hyp_hnqmap1rn_1
  have p0001 := (Nominal.classEqRefl (synChnord A))
  have p0002 :=
    @gEleq2i (synChnord A) (synCqs (synChwcn A) (synChwniso A)) (.cv z) p0001
  have p0003 :=
    @gBiimpi (.classMem (.cv z) (synChnord A))
      (.classMem (.cv z) (synCqs (synChwcn A) (synChwniso A))) p0002
  have p0004 :=
    @gElqsi u (synChwcn A) (.cv z) (synChwniso A) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0005 :=
    @gSyl (.classMem (.cv z) (synChnord A))
      (.classMem (.cv z) (synCqs (synChwcn A) (synChwniso A)))
      (synWrex u (synChwcn A) (.classEq (.cv z) (synCec (.cv u) (synChwniso A))))
      p0003 p0004
  have p0006 := @gSnelpw1 (.cv u) (synChwcn A)
  have p0007 :=
    @gBiimpri (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0006
  have p0008 :=
    @gAdantr (.classMem (.cv u) (synChwcn A))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classEq (.cv z) (synCec (.cv u) (synChwniso A))) p0007
  have p0009 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classEq (.cv z) (synCec (.cv u) (synChwniso A)))
  have p0010 := @gHnqmap1val u A dv_cache_0004 hyp_hnqmap1rn_1
  have p0011 :=
    @gAdantr (.classMem (.cv u) (synChwcn A))
      (.classEq (synCfv (synChnqmap1 A) (synCsn (.cv u))) (synCec (.cv u) (synChwniso A)))
      (.classEq (.cv z) (synCec (.cv u) (synChwniso A))) p0010
  have p0012 :=
    @gEqtr4d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (.cv z) (synCec (.cv u) (synChwniso A))))
      (.cv z) (synCec (.cv u) (synChwniso A))
      (synCfv (synChnqmap1 A) (synCsn (.cv u))) p0009 p0011
  have p0013 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (.cv z) (synCec (.cv u) (synChwniso A))))
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
      (.classEq (.cv z) (synCfv (synChnqmap1 A) (synCsn (.cv u)))) p0008 p0012
  have p0014 := @gFveq2 (.cv q) (synCsn (.cv u)) (synChnqmap1 A)
  have p0015 :=
    @gEqeq2d (.classEq (.cv q) (synCsn (.cv u))) (synCfv (synChnqmap1 A) (.cv q))
      (synCfv (synChnqmap1 A) (synCsn (.cv u))) (.cv z) p0014
  have p0016 :=
    @gRspcev (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q)))
      (.classEq (.cv z) (synCfv (synChnqmap1 A) (synCsn (.cv u)))) q (synCsn (.cv u))
      (synCpw1 (synChwcn A)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0015
  have p0017 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classEq (.cv z) (synCec (.cv u) (synChwniso A))))
      (synWa (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn A)))
        (.classEq (.cv z) (synCfv (synChnqmap1 A) (synCsn (.cv u)))))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q))))
      p0013 p0016
  have p0018 :=
    @gRexlimiva (.classEq (.cv z) (synCec (.cv u) (synChwniso A)))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q))))
      u (synChwcn A) dv_cache_0008 p0017
  have p0019 :=
    @gSyl (.classMem (.cv z) (synChnord A))
      (synWrex u (synChwcn A) (.classEq (.cv z) (synCec (.cv u) (synChwniso A))))
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q))))
      p0005 p0018
  have p0020 :=
    @gRgen
      (synWrex q (synCpw1 (synChwcn A))
        (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q))))
      z (synChnord A) p0019
  have p0021 :=
    @gPm32i (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
      (synWral z (synChnord A) (synWrex q (synCpw1 (synChwcn A))
          (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q)))))
      p0000 p0020
  have p0022 :=
    @gDffo3 q z (synCpw1 (synChwcn A)) (synChnord A) (synChnqmap1 A) dv_cache_0006
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0023 :=
    @gMpbir (synWfo (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
      (synWa (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
        (synWral z (synChnord A) (synWrex q (synCpw1 (synChwcn A))
            (.classEq (.cv z) (synCfv (synChnqmap1 A) (.cv q))))))
      p0021 p0022
  have p0024 := @gDffo2 (synCpw1 (synChwcn A)) (synChnord A) (synChnqmap1 A)
  have p0025 :=
    @gMpbi (synWfo (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
      (synWa (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
        (.classEq (synCrn (synChnqmap1 A)) (synChnord A)))
      p0023 p0024
  have p0026 :=
    @gSimpri (synWf (synChnqmap1 A) (synCpw1 (synChwcn A)) (synChnord A))
      (.classEq (synCrn (synChnqmap1 A)) (synChnord A)) p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_brlnker`. -/
@[expose]
noncomputable def gBrlnker (R : Class) (X : Class) (Y : Class) :
    Nominal.NPrf
      (synWb (synWbr X (synClnker R) Y) (synWa (synWbr X R Y) (synWbr Y R X))) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnker R))
  have p0001 := @gBreqi X Y (synClnker R) (synCin R (synCcnv R)) p0000
  have p0002 := @gBrin X Y R (synCcnv R)
  have p0003 := @gBrcnv X Y R
  have p0004 := @gAnbi2i (synWbr X (synCcnv R) Y) (synWbr Y R X) (synWbr X R Y) p0003
  have p0005 :=
    @gBitri (synWbr X (synCin R (synCcnv R)) Y)
      (synWa (synWbr X R Y) (synWbr X (synCcnv R) Y))
      (synWa (synWbr X R Y) (synWbr Y R X)) p0002 p0004
  have p0006 :=
    @gBitri (synWbr X (synClnker R) Y) (synWbr X (synCin R (synCcnv R)) Y)
      (synWa (synWbr X R Y) (synWbr Y R X)) p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_lnkerex`. -/
@[expose]
noncomputable def gLnkerex (R : Class)
    (hyp_lnkerex_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classMem (synClnker R) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synClnker R))
  have p0001 := @gCnvex R hyp_lnkerex_1
  have p0002 := @gInex R (synCcnv R) hyp_lnkerex_1 p0001
  have p0003 := @gEqeltri (synClnker R) (synCin R (synCcnv R)) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ellnquo`. -/
@[expose]
noncomputable def gEllnquo (x : Var) (A : Class) (B : Class) (R : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_ellnquo_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem B (synClnquo R A))
        (synWrex x A (.classEq B (synCec (.cv x) (synClnker R))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synClnker R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, dv_R_x,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synClnquo R A))
  have p0001 := @gEleq2i (synClnquo R A) (synCqs A (synClnker R)) B p0000
  have p0002 :=
    @gElqs x A B (synClnker R) dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_ellnquo_1
  have p0003 :=
    @gBitri (.classMem B (synClnquo R A)) (.classMem B (synCqs A (synClnker R)))
      (synWrex x A (.classEq B (synCec (.cv x) (synClnker R)))) p0001 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part054`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_lefinssvvk`. -/
@[expose]
noncomputable def gLefinssvvk :
    Nominal.NPrf (synWss (synClefin) (synCxpk (synCvv) (synCvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : w ≠ x := by exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0002 : w ≠ y := by
    clear dv_cache_0001
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0003 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ z from (by exact fresh_w_ne_z))
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLefin x y z w
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gOpkabssvvki (synWrex w (synCnnc) (.classEq (.cv z) (synCplc (.cv y) (.cv w)))) x
      y z (synClefin) dv_cache_0004 dv_cache_0005 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ltfinssvvk`. -/
@[expose]
noncomputable def gLtfinssvvk :
    Nominal.NPrf (synWss (synCltfin) (synCxpk (synCvv) (synCvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let m : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_m_ne_n : m ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_p : m ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : m ≠ n := by exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0002 : m ≠ p := by
    clear dv_cache_0001
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0003 : m ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0004 : n ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0005 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0006 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0007 : x ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ m from (by exact fresh_x_ne_m))
  have dv_cache_0008 : x ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ n from (by exact fresh_x_ne_n))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLtfin x m n p
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gOpkabssvvki
      (synWa (synWne (.cv m) (synC0)) (synWrex p (synCnnc)
          (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c)))))
      x m n (synCltfin) dv_cache_0007 dv_cache_0008 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ltfinunidkssvvk`. -/
@[expose]
noncomputable def gLtfinunidkssvvk :
    Nominal.NPrf
      (synWss (synCun (synCltfin) (synCidk)) (synCxpk (synCvv) (synCvv))) :=
  by
  have p0000 := @gLtfinssvvk
  have p0001 := @gIdkssvvk
  have p0002 :=
    @gUnssi (synCltfin) (synCidk) (synCxpk (synCvv) (synCvv)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ellefinunidk`. -/
@[expose]
noncomputable def gEllefinunidk (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCun (synCltfin) (synCidk)))
          (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))) :=
  by
  have p0000 := @gElun (synCopk A B) (synCltfin) (synCidk)
  have p0001 :=
    @gA1i
      (synWb (.classMem (synCopk A B) (synCun (synCltfin) (synCidk)))
        (synWo (.classMem (synCopk A B) (synCltfin)) (.classMem (synCopk A B) (synCidk))))
      (synWa (.classMem A V) (.classMem B W)) p0000
  have p0002 := @gOpkelidkg A B V W
  have p0003 :=
    @gOrbi2d (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCopk A B) (synCidk)) (.classEq A B)
      (.classMem (synCopk A B) (synCltfin)) p0002
  have p0004 :=
    @gBitrd (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCopk A B) (synCun (synCltfin) (synCidk)))
      (synWo (.classMem (synCopk A B) (synCltfin)) (.classMem (synCopk A B) (synCidk)))
      (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_lefinlteq0`. -/
@[expose]
noncomputable def gLefinlteq0 (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (synWb (.classMem (synCopk A B) (synClefin)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_V, fresh_x_not_B, fresh_x_not_W,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gSimp1 (.classMem A V) (.classMem B W) (.classEq A (synC0))
  have p0001 := @gSimp2 (.classMem A V) (.classMem B W) (.classEq A (synC0))
  have p0002 :=
    @gJca (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classMem A V)
      (.classMem B W) p0000 p0001
  have p0003 := @gOpklefing x A B V W dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gSyl (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (synWa (.classMem A V) (.classMem B W))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x)))))
      p0002 p0003
  have p0005 :=
    @gSimpl
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq B (synCplc A (.cv x)))
  have p0006 :=
    @gSimpl (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classMem (.cv x) (synCnnc))
  have p0007 := @gSimp3 (.classMem A V) (.classMem B W) (.classEq A (synC0))
  have p0008 :=
    @gSyl
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classEq A (synC0)) p0006 p0007
  have p0009 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
          (.classMem (.cv x) (synCnnc))) (.classEq B (synCplc A (.cv x))))
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq A (synC0)) p0005 p0008
  have p0010 :=
    @gSimpr
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq B (synCplc A (.cv x)))
  have p0012 := @gAddccom A (.cv x)
  have p0013 :=
    @gA1i (.classEq (synCplc A (.cv x)) (synCplc (.cv x) A))
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      p0012
  have p0017 :=
    @gAddceq2d
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      A (synC0) (.cv x) p0008
  have p0018 :=
    @gEqtrd
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (synCplc A (.cv x)) (synCplc (.cv x) A) (synCplc (.cv x) (synC0)) p0013 p0017
  have p0019 := @gAddcnul1 (.cv x)
  have p0020 :=
    @gA1i (.classEq (synCplc (.cv x) (synC0)) (synC0))
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      p0019
  have p0021 :=
    @gEqtrd
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (synCplc A (.cv x)) (synCplc (.cv x) (synC0)) (synC0) p0018 p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
          (.classMem (.cv x) (synCnnc))) (.classEq B (synCplc A (.cv x))))
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq (synCplc A (.cv x)) (synC0)) p0005 p0021
  have p0023 :=
    @gEqtrd
      (synWa (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
          (.classMem (.cv x) (synCnnc))) (.classEq B (synCplc A (.cv x))))
      B (synCplc A (.cv x)) (synC0) p0010 p0022
  have p0024 :=
    @gEqcomd
      (synWa (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
          (.classMem (.cv x) (synCnnc))) (.classEq B (synCplc A (.cv x))))
      B (synC0) p0023
  have p0025 :=
    @gEqtrd
      (synWa (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
          (.classMem (.cv x) (synCnnc))) (.classEq B (synCplc A (.cv x))))
      A (synC0) B p0009 p0024
  have p0026 :=
    @gEx
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq B (synCplc A (.cv x))) (.classEq A B) p0025
  have p0027 :=
    @gRexlimdva (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classEq B (synCplc A (.cv x))) (.classEq A B) x (synCnnc) dv_cache_0003
      dv_cache_0004 p0026
  have p0028 :=
    @gSylbid (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classMem (synCopk A B) (synClefin))
      (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x)))) (.classEq A B) p0004 p0027
  have p0029 :=
    @gSimpl (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classEq A B)
  have p0031 :=
    @gSyl
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classEq A B))
      (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classMem A V)
      p0029 p0000
  have p0032 := @gLefinrflx A V
  have p0033 :=
    @gSyl
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classEq A B))
      (.classMem A V) (.classMem (synCopk A A) (synClefin)) p0031 p0032
  have p0034 :=
    @gSimpr (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classEq A B)
  have p0035 := @gOpkeq2 A B A
  have p0036 :=
    @gSyl
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classEq A B))
      (.classEq A B) (.classEq (synCopk A A) (synCopk A B)) p0034 p0035
  have p0037 :=
    @gEleq1d
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classEq A B))
      (synCopk A A) (synCopk A B) (synClefin) p0036
  have p0038 :=
    @gMpbid
      (synWa (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classEq A B))
      (.classMem (synCopk A A) (synClefin)) (.classMem (synCopk A B) (synClefin))
      p0033 p0037
  have p0039 :=
    @gEx (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0))) (.classEq A B)
      (.classMem (synCopk A B) (synClefin)) p0038
  have p0040 :=
    @gImpbid (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (.classMem (synCopk A B) (synClefin)) (.classEq A B) p0028 p0039
  exact p0040

/-- Checked nominal proof certificate identified upstream as `g_lefinlteqall`. -/
@[expose]
noncomputable def gLefinlteqall (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synClefin))
          (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 := @gSimpl (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0))
  have p0001 := @gSimpl (.classMem A V) (.classMem B W)
  have p0002 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0)))
      (synWa (.classMem A V) (.classMem B W)) (.classMem A V) p0000 p0001
  have p0004 := @gSimpr (.classMem A V) (.classMem B W)
  have p0005 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0)))
      (synWa (.classMem A V) (.classMem B W)) (.classMem B W) p0000 p0004
  have p0006 := @gSimpr (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0))
  have p0007 :=
    @gN3jca (synWa (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0)))
      (.classMem A V) (.classMem B W) (synWne A (synC0)) p0002 p0005 p0006
  have p0008 := @gLefinlteq A B V W
  have p0009 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0)))
      (synW3a (.classMem A V) (.classMem B W) (synWne A (synC0)))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))
      p0007 p0008
  have p0010 :=
    @gEx (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))
      p0009
  have p0011 :=
    @gSimpl (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0)))
  have p0013 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (synWa (.classMem A V) (.classMem B W)) (.classMem A V) p0011 p0001
  have p0016 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (synWa (.classMem A V) (.classMem B W)) (.classMem B W) p0011 p0004
  have p0017 :=
    @gSimpr (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0)))
  have p0018 := @gNne A (synC0)
  have p0019 :=
    @gA1i (synWb (.neg (synWne A (synC0))) (.classEq A (synC0)))
      (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0)))) p0018
  have p0020 :=
    @gMpbid (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.neg (synWne A (synC0))) (.classEq A (synC0)) p0017 p0019
  have p0021 :=
    @gN3jca
      (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.classMem A V) (.classMem B W) (.classEq A (synC0)) p0013 p0016 p0020
  have p0022 := @gLefinlteq0 A B V W
  have p0023 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (synW3a (.classMem A V) (.classMem B W) (.classEq A (synC0)))
      (synWb (.classMem (synCopk A B) (synClefin)) (.classEq A B)) p0021 p0022
  have p0026 := @gOpkltfing x A B V W dv_cache_0001 dv_cache_0002
  have p0027 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (synWa (.classMem A V) (.classMem B W))
      (synWb (.classMem (synCopk A B) (synCltfin)) (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))))
      p0011 p0026
  have p0028 :=
    @gSimpl (synWne A (synC0))
      (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
  have p0029 :=
    @gA1i
      (.imp (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
        (synWne A (synC0)))
      (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0)))) p0028
  have p0030 :=
    @gSylbid
      (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.classMem (synCopk A B) (synCltfin))
      (synWa (synWne A (synC0))
        (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
      (synWne A (synC0)) p0027 p0029
  have p0031 :=
    @gCon3d (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.classMem (synCopk A B) (synCltfin)) (synWne A (synC0)) p0030
  have p0032 :=
    @gMpd (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.neg (synWne A (synC0))) (.neg (.classMem (synCopk A B) (synCltfin))) p0017
      p0031
  have p0033 := @gBiorf (.classMem (synCopk A B) (synCltfin)) (.classEq A B)
  have p0034 :=
    @gSyl (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.neg (.classMem (synCopk A B) (synCltfin)))
      (synWb (.classEq A B) (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))
      p0032 p0033
  have p0035 :=
    @gBitrd (synWa (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0))))
      (.classMem (synCopk A B) (synClefin)) (.classEq A B)
      (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)) p0023 p0034
  have p0036 :=
    @gEx (synWa (.classMem A V) (.classMem B W)) (.neg (synWne A (synC0)))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))
      p0035
  have p0037 :=
    @gPm261d (synWa (.classMem A V) (.classMem B W)) (synWne A (synC0))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))
      p0010 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_lefinunidk`. -/
@[expose]
noncomputable def gLefinunidk :
    Nominal.NPrf (.classEq (synClefin) (synCun (synCltfin) (synCidk))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((synClefin)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synClefin)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCun (synCltfin) (synCidk))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCun (synCltfin) (synCidk))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gLefinssvvk
  have p0001 := @gLtfinunidkssvvk
  have p0002 := @gTru
  have p0003 := @gVex x
  have p0004 := @gA1i (.classMem (.cv x) (synCvv)) synWtru p0003
  have p0005 := @gVex y
  have p0006 := @gA1i (.classMem (.cv y) (synCvv)) synWtru p0005
  have p0007 :=
    @gJca synWtru (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)) p0004
      p0006
  have p0008 := Nominal.mp p0002 p0007
  have p0009 := @gLefinlteqall (.cv x) (.cv y) (synCvv) (synCvv)
  have p0010 := Nominal.mp p0008 p0009
  have p0018 := @gEllefinunidk (.cv x) (.cv y) (synCvv) (synCvv)
  have p0019 := Nominal.mp p0008 p0018
  have p0020 :=
    @gBitr4i (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
      (synWo (.classMem (synCopk (.cv x) (.cv y)) (synCltfin)) (.classEq (.cv x) (.cv y)))
      (.classMem (synCopk (.cv x) (.cv y)) (synCun (synCltfin) (synCidk))) p0010 p0019
  have p0021 :=
    @gEqrelkriiv x y (synClefin) (synCun (synCltfin) (synCidk)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0000 p0001 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_lefinex`. -/
@[expose]
noncomputable def gLefinex : Nominal.NPrf (.classMem (synClefin) (synCvv)) :=
  by
  have p0000 := @gLefinunidk
  have p0001 := @gLtfinex
  have p0002 := @gIdkex
  have p0003 := @gUnex (synCltfin) (synCidk) p0001 p0002
  have p0004 :=
    @gEqeltri (synClefin) (synCun (synCltfin) (synCidk)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_kqrelbrg`. -/
@[expose]
noncomputable def gKqrelbrg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem B V) (.classMem C W))
        (synWb (.classMem (synCop B C) (synCkqrel A)) (.classMem (synCopk B C) A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0007 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (synCopk B C) A)).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classMem (synCopk B C) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_C, fresh_y_not_A, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfKqrel x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEleq2i (synCkqrel A) (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A))
      (synCop B C) p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (synCop B C) (synCkqrel A)) (.classMem (synCop B C)
          (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A))))
      (synWa (.classMem B V) (.classMem C W)) p0001
  have p0003 := @gOpkeq1 (.cv x) B (.cv y)
  have p0004 :=
    @gEleq1d (.classEq (.cv x) B) (synCopk (.cv x) (.cv y)) (synCopk B (.cv y)) A p0003
  have p0005 := @gOpkeq2 (.cv y) C B
  have p0006 := @gEleq1d (.classEq (.cv y) C) (synCopk B (.cv y)) (synCopk B C) A p0005
  have p0007 :=
    @gOpelopabg (.classMem (synCopk (.cv x) (.cv y)) A)
      (.classMem (synCopk B (.cv y)) A) (.classMem (synCopk B C) A) x y B C V W
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0003 p0004 p0006
  have p0008 :=
    @gBitrd (synWa (.classMem B V) (.classMem C W))
      (.classMem (synCop B C) (synCkqrel A))
      (.classMem (synCop B C) (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A)))
      (.classMem (synCopk B C) A) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_kqlefinbr`. -/
@[expose]
noncomputable def gKqlefinbr (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (synWbr A (synCkqrel (synClefin)) B)
          (.classMem (synCopk A B) (synClefin)))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr A (synCkqrel (synClefin)) B))
  have p0001 :=
    @gA1i
      (synWb (synWbr A (synCkqrel (synClefin)) B)
        (.classMem (synCop A B) (synCkqrel (synClefin))))
      (synWa (.classMem A V) (.classMem B W)) p0000
  have p0002 := @gKqrelbrg (synClefin) A B V W
  have p0003 :=
    @gBitrd (synWa (.classMem A V) (.classMem B W))
      (synWbr A (synCkqrel (synClefin)) B)
      (.classMem (synCop A B) (synCkqrel (synClefin)))
      (.classMem (synCopk A B) (synClefin)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_lefintrnn`. -/
@[expose]
noncomputable def gLefintrnn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
        (.imp (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B C) (synClefin)))
          (.classMem (synCopk A C) (synClefin)))) :=
  by
  have p0000 :=
    @gSimpr
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B C) (synClefin)))
  have p0001 :=
    @gSimpr (.classMem (synCopk A B) (synClefin))
      (.classMem (synCopk B C) (synClefin))
  have p0002 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B C) (synClefin)))
      (.classMem (synCopk B C) (synClefin)) p0000 p0001
  have p0003 :=
    @gSimpl
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B C) (synClefin)))
  have p0004 :=
    @gSimp2 (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc))
  have p0005 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (.classMem B (synCnnc)) p0003 p0004
  have p0007 :=
    @gSimp3 (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc))
  have p0008 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (.classMem C (synCnnc)) p0003 p0007
  have p0009 :=
    @gJca
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem B (synCnnc)) (.classMem C (synCnnc)) p0005 p0008
  have p0010 := @gLenltfin B C
  have p0011 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synWa (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWb (.classMem (synCopk B C) (synClefin))
        (.neg (.classMem (synCopk C B) (synCltfin))))
      p0009 p0010
  have p0012 :=
    @gBiimpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk B C) (synClefin))
      (.neg (.classMem (synCopk C B) (synCltfin))) p0011
  have p0013 :=
    @gMpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk B C) (synClefin))
      (.neg (.classMem (synCopk C B) (synCltfin))) p0002 p0012
  have p0015 :=
    @gSimpl (.classMem (synCopk A B) (synClefin))
      (.classMem (synCopk B C) (synClefin))
  have p0016 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B C) (synClefin)))
      (.classMem (synCopk A B) (synClefin)) p0000 p0015
  have p0018 :=
    @gSimp1 (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc))
  have p0019 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (.classMem A (synCnnc)) p0003 p0018
  have p0020 := @gElex A (synCnnc)
  have p0021 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem A (synCnnc)) (.classMem A (synCvv)) p0019 p0020
  have p0025 := @gElex B (synCnnc)
  have p0026 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem B (synCnnc)) (.classMem B (synCvv)) p0005 p0025
  have p0027 :=
    @gJca
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem A (synCvv)) (.classMem B (synCvv)) p0021 p0026
  have p0028 := @gLefinlteqall A B (synCvv) (synCvv)
  have p0029 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)))
      p0027 p0028
  have p0030 :=
    @gBiimpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk A B) (synClefin))
      (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)) p0029
  have p0031 :=
    @gMpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk A B) (synClefin))
      (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B)) p0016 p0030
  have p0041 :=
    @gN3jca
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem C (synCnnc)) (.classMem A (synCnnc)) (.classMem B (synCnnc)) p0008
      p0019 p0005
  have p0042 := @gLtfintr C A B
  have p0043 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synW3a (.classMem C (synCnnc)) (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.imp (synWa (.classMem (synCopk C A) (synCltfin))
          (.classMem (synCopk A B) (synCltfin))) (.classMem (synCopk C B) (synCltfin)))
      p0041 p0042
  have p0044 :=
    @gExp3a
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk C A) (synCltfin)) (.classMem (synCopk A B) (synCltfin))
      (.classMem (synCopk C B) (synCltfin)) p0043
  have p0045 :=
    @gCom23
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk C A) (synCltfin)) (.classMem (synCopk A B) (synCltfin))
      (.classMem (synCopk C B) (synCltfin)) p0044
  have p0046 := @gOpkeq2 A B C
  have p0047 := @gEleq1d (.classEq A B) (synCopk C A) (synCopk C B) (synCltfin) p0046
  have p0048 :=
    @gBiimpd (.classEq A B) (.classMem (synCopk C A) (synCltfin))
      (.classMem (synCopk C B) (synCltfin)) p0047
  have p0049 :=
    @gA1i
      (.imp (.classEq A B) (.imp (.classMem (synCopk C A) (synCltfin))
          (.classMem (synCopk C B) (synCltfin))))
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      p0048
  have p0050 :=
    @gJaod
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk A B) (synCltfin))
      (.imp (.classMem (synCopk C A) (synCltfin)) (.classMem (synCopk C B) (synCltfin)))
      (.classEq A B) p0045 p0049
  have p0051 :=
    @gMpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synWo (.classMem (synCopk A B) (synCltfin)) (.classEq A B))
      (.imp (.classMem (synCopk C A) (synCltfin)) (.classMem (synCopk C B) (synCltfin)))
      p0031 p0050
  have p0052 :=
    @gCon3d
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk C A) (synCltfin)) (.classMem (synCopk C B) (synCltfin))
      p0051
  have p0053 :=
    @gMpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.neg (.classMem (synCopk C B) (synCltfin)))
      (.neg (.classMem (synCopk C A) (synCltfin))) p0013 p0052
  have p0060 :=
    @gJca
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem A (synCnnc)) (.classMem C (synCnnc)) p0019 p0008
  have p0061 := @gLenltfin A C
  have p0062 :=
    @gSyl
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
      (synWb (.classMem (synCopk A C) (synClefin))
        (.neg (.classMem (synCopk C A) (synCltfin))))
      p0060 p0061
  have p0063 :=
    @gBiimprd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.classMem (synCopk A C) (synClefin))
      (.neg (.classMem (synCopk C A) (synCltfin))) p0062
  have p0064 :=
    @gMpd
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc))) (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B C) (synClefin))))
      (.neg (.classMem (synCopk C A) (synCltfin)))
      (.classMem (synCopk A C) (synClefin)) p0053 p0063
  have p0065 :=
    @gEx
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B C) (synClefin)))
      (.classMem (synCopk A C) (synClefin)) p0064
  exact p0065


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part055`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_lefinantinn`. -/
@[expose]
noncomputable def gLefinantinn (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.imp
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin))) (.classEq A B))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWne A (synC0))
  have p0001 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
  have p0002 := @gSimpl (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.classMem A (synCnnc))
      p0001 p0002
  have p0004 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem A (synCnnc)) p0000 p0003
  have p0007 := @gSimpr (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.classMem B (synCnnc))
      p0001 p0007
  have p0009 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem B (synCnnc)) p0000 p0008
  have p0010 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWne A (synC0))
  have p0011 :=
    @gN3jca
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWne A (synC0)) p0004 p0009
      p0010
  have p0012 := @gLtfintri A B
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWne A (synC0)))
      (synW3o (.classMem (synCopk A B) (synCltfin)) (.classEq A B)
        (.classMem (synCopk B A) (synCltfin)))
      p0011 p0012
  have p0015 :=
    @gSimpr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
  have p0016 :=
    @gSimpr (.classMem (synCopk A B) (synClefin))
      (.classMem (synCopk B A) (synClefin))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      (.classMem (synCopk B A) (synClefin)) p0015 p0016
  have p0021 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCnnc)) (.classMem A (synCnnc)) p0007 p0002
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem B (synCnnc)) (.classMem A (synCnnc))) p0001 p0021
  have p0023 := @gLenltfin B A
  have p0024 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem B (synCnnc)) (.classMem A (synCnnc)))
      (synWb (.classMem (synCopk B A) (synClefin))
        (.neg (.classMem (synCopk A B) (synCltfin))))
      p0022 p0023
  have p0025 :=
    @gBiimpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem (synCopk B A) (synClefin))
      (.neg (.classMem (synCopk A B) (synCltfin))) p0024
  have p0026 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem (synCopk B A) (synClefin))
      (.neg (.classMem (synCopk A B) (synCltfin))) p0017 p0025
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.neg (.classMem (synCopk A B) (synCltfin))) p0000 p0026
  have p0028 :=
    @gPm221d
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (.classMem (synCopk A B) (synCltfin)) (.classEq A B) p0027
  have p0029 := @gId (.classEq A B)
  have p0030 :=
    @gA1i (.imp (.classEq A B) (.classEq A B))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      p0029
  have p0033 :=
    @gSimpl (.classMem (synCopk A B) (synClefin))
      (.classMem (synCopk B A) (synClefin))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      (.classMem (synCopk A B) (synClefin)) p0015 p0033
  have p0036 := @gLenltfin A B
  have p0037 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWb (.classMem (synCopk A B) (synClefin))
        (.neg (.classMem (synCopk B A) (synCltfin))))
      p0001 p0036
  have p0038 :=
    @gBiimpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem (synCopk A B) (synClefin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0037
  have p0039 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem (synCopk A B) (synClefin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0034 p0038
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0000 p0039
  have p0041 :=
    @gPm221d
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (.classMem (synCopk B A) (synCltfin)) (.classEq A B) p0040
  have p0042 :=
    @gN3jaod
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (.classMem (synCopk A B) (synCltfin)) (.classEq A B) (.classEq A B)
      (.classMem (synCopk B A) (synCltfin)) p0028 p0030 p0041
  have p0043 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (synWne A (synC0)))
      (synW3o (.classMem (synCopk A B) (synCltfin)) (.classEq A B)
        (.classMem (synCopk B A) (synCltfin)))
      (.classEq A B) p0013 p0042
  have p0044 :=
    @gEx
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWne A (synC0)) (.classEq A B) p0043
  have p0045 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.neg (synWne A (synC0)))
  have p0049 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem (synCopk A B) (synClefin)) p0045 p0034
  have p0054 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem A (synCnnc)) p0045 p0003
  have p0055 := @gElex A (synCnnc)
  have p0056 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (.classMem A (synCnnc)) (.classMem A (synCvv)) p0054 p0055
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.classMem B (synCnnc)) p0045 p0008
  have p0062 := @gElex B (synCnnc)
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (.classMem B (synCnnc)) (.classMem B (synCvv)) p0061 p0062
  have p0064 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.neg (synWne A (synC0)))
  have p0065 := @gNne A (synC0)
  have p0066 :=
    @gA1i (synWb (.neg (synWne A (synC0))) (.classEq A (synC0)))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      p0065
  have p0067 :=
    @gMpbid
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (.neg (synWne A (synC0))) (.classEq A (synC0)) p0064 p0066
  have p0068 :=
    @gN3jca
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (.classMem A (synCvv)) (.classMem B (synCvv)) (.classEq A (synC0)) p0056 p0063
      p0067
  have p0069 := @gLefinlteq0 A B (synCvv) (synCvv)
  have p0070 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (synW3a (.classMem A (synCvv)) (.classMem B (synCvv)) (.classEq A (synC0)))
      (synWb (.classMem (synCopk A B) (synClefin)) (.classEq A B)) p0068 p0069
  have p0071 :=
    @gMpbid
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B A) (synClefin)))) (.neg (synWne A (synC0))))
      (.classMem (synCopk A B) (synClefin)) (.classEq A B) p0049 p0070
  have p0072 :=
    @gEx
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (.neg (synWne A (synC0))) (.classEq A B) p0071
  have p0073 :=
    @gPm261d
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin))))
      (synWne A (synC0)) (.classEq A B) p0044 p0072
  have p0074 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      (.classEq A B) p0073
  exact p0074

/-- Checked nominal proof certificate identified upstream as `g_lefinconnexnn`. -/
@[expose]
noncomputable def gLefinconnexnn (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWo (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synClefin)))) :=
  by
  have p0000 := @gSimpr (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0001 := @gElex B (synCnnc)
  have p0002 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCnnc)) (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpl (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0004 := @gElex A (synCnnc)
  have p0005 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem A (synCnnc)) (.classMem A (synCvv)) p0003 p0004
  have p0006 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCvv)) (.classMem A (synCvv)) p0002 p0005
  have p0007 := @gLtlefin B A (synCvv) (synCvv)
  have p0008 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem B (synCvv)) (.classMem A (synCvv)))
      (.imp (.classMem (synCopk B A) (synCltfin)) (.classMem (synCopk B A) (synClefin)))
      p0006 p0007
  have p0009 :=
    @gOlc (.classMem (synCopk B A) (synClefin)) (.classMem (synCopk A B) (synClefin))
  have p0010 :=
    @gSyl6 (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B A) (synCltfin)) (.classMem (synCopk B A) (synClefin))
      (synWo (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      p0008 p0009
  have p0011 := @gLenltfin A B
  have p0012 :=
    @gBiimprd (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synClefin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0011
  have p0013 :=
    @gOrc (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin))
  have p0014 :=
    @gSyl6 (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.neg (.classMem (synCopk B A) (synCltfin)))
      (.classMem (synCopk A B) (synClefin))
      (synWo (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      p0012 p0013
  have p0015 :=
    @gPm261d (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B A) (synCltfin))
      (synWo (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synClefin)))
      p0010 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_finleor`. -/
@[expose]
noncomputable def gFinleor :
    Nominal.NPrf (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc)) :=
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
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((synCnnc)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCkqrel (synClefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : y ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : z ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @gTru
  have p0001 := @gLefinex
  have p0002 := @gKqrelex (synClefin) p0001
  have p0003 := @gA1i (.classMem (synCkqrel (synClefin)) (synCvv)) synWtru p0002
  have p0004 := @gNncex
  have p0005 := @gA1i (.classMem (synCnnc) (synCvv)) synWtru p0004
  have p0006 := @gSimpr synWtru (.classMem (.cv x) (synCnnc))
  have p0007 := @gElex (.cv x) (synCnnc)
  have p0008 :=
    @gSyl (synWa synWtru (.classMem (.cv x) (synCnnc))) (.classMem (.cv x) (synCnnc))
      (.classMem (.cv x) (synCvv)) p0006 p0007
  have p0009 := @gLefinrflx (.cv x) (synCvv)
  have p0010 :=
    @gSyl (synWa synWtru (.classMem (.cv x) (synCnnc))) (.classMem (.cv x) (synCvv))
      (.classMem (synCopk (.cv x) (.cv x)) (synClefin)) p0008 p0009
  have p0017 :=
    @gJca (synWa synWtru (.classMem (.cv x) (synCnnc))) (.classMem (.cv x) (synCvv))
      (.classMem (.cv x) (synCvv)) p0008 p0008
  have p0018 := @gKqlefinbr (.cv x) (.cv x) (synCvv) (synCvv)
  have p0019 :=
    @gSyl (synWa synWtru (.classMem (.cv x) (synCnnc)))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv x) (synCvv)))
      (synWb (synWbr (.cv x) (synCkqrel (synClefin)) (.cv x))
        (.classMem (synCopk (.cv x) (.cv x)) (synClefin)))
      p0017 p0018
  have p0020 :=
    @gMpbird (synWa synWtru (.classMem (.cv x) (synCnnc)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv x))
      (.classMem (synCopk (.cv x) (.cv x)) (synClefin)) p0010 p0019
  have p0021 :=
    @gSimp3 synWtru
      (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
        (.classMem (.cv z) (synCnnc)))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
  have p0022 :=
    @gSimpl (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
  have p0023 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y)) p0021 p0022
  have p0024 :=
    @gSimp2 synWtru
      (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
        (.classMem (.cv z) (synCnnc)))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
  have p0025 :=
    @gSimp1 (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
      (.classMem (.cv z) (synCnnc))
  have p0026 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
        (.classMem (.cv z) (synCnnc)))
      (.classMem (.cv x) (synCnnc)) p0024 p0025
  have p0028 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv x) (synCnnc)) (.classMem (.cv x) (synCvv)) p0026 p0007
  have p0030 :=
    @gSimp2 (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
      (.classMem (.cv z) (synCnnc))
  have p0031 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
        (.classMem (.cv z) (synCnnc)))
      (.classMem (.cv y) (synCnnc)) p0024 p0030
  have p0032 := @gElex (.cv y) (synCnnc)
  have p0033 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCvv)) p0031 p0032
  have p0034 :=
    @gJca
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)) p0028 p0033
  have p0035 := @gKqlefinbr (.cv x) (.cv y) (synCvv) (synCvv)
  have p0036 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
      (synWb (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (.classMem (synCopk (.cv x) (.cv y)) (synClefin)))
      p0034 p0035
  have p0037 :=
    @gMpbid
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin)) p0023 p0036
  have p0039 :=
    @gSimpr (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
  have p0040 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) p0021 p0039
  have p0047 :=
    @gSimp3 (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
      (.classMem (.cv z) (synCnnc))
  have p0048 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
        (.classMem (.cv z) (synCnnc)))
      (.classMem (.cv z) (synCnnc)) p0024 p0047
  have p0049 := @gElex (.cv z) (synCnnc)
  have p0050 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv z) (synCnnc)) (.classMem (.cv z) (synCvv)) p0048 p0049
  have p0051 :=
    @gJca
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv)) p0033 p0050
  have p0052 := @gKqlefinbr (.cv y) (.cv z) (synCvv) (synCvv)
  have p0053 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv)))
      (synWb (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
        (.classMem (synCopk (.cv y) (.cv z)) (synClefin)))
      p0051 p0052
  have p0054 :=
    @gMpbid
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
      (.classMem (synCopk (.cv y) (.cv z)) (synClefin)) p0040 p0053
  have p0055 :=
    @gJca
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
      (.classMem (synCopk (.cv y) (.cv z)) (synClefin)) p0037 p0054
  have p0057 := @gLefintrnn (.cv x) (.cv y) (.cv z)
  have p0058 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
        (.classMem (.cv z) (synCnnc)))
      (.imp (synWa (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
          (.classMem (synCopk (.cv y) (.cv z)) (synClefin)))
        (.classMem (synCopk (.cv x) (.cv z)) (synClefin)))
      p0024 p0057
  have p0059 :=
    @gMpd
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWa (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
        (.classMem (synCopk (.cv y) (.cv z)) (synClefin)))
      (.classMem (synCopk (.cv x) (.cv z)) (synClefin)) p0055 p0058
  have p0070 :=
    @gJca
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (.classMem (.cv x) (synCvv)) (.classMem (.cv z) (synCvv)) p0028 p0050
  have p0071 := @gKqlefinbr (.cv x) (.cv z) (synCvv) (synCvv)
  have p0072 :=
    @gSyl
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv z) (synCvv)))
      (synWb (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))
        (.classMem (synCopk (.cv x) (.cv z)) (synClefin)))
      p0070 p0071
  have p0073 :=
    @gMpbird
      (synW3a synWtru (synW3a (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
          (.classMem (.cv z) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv z))
      (.classMem (synCopk (.cv x) (.cv z)) (synClefin)) p0059 p0072
  have p0074 :=
    @gSimp3 synWtru
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
  have p0075 :=
    @gSimpl (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
  have p0076 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y)) p0074 p0075
  have p0077 :=
    @gSimp2 synWtru
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
  have p0078 := @gSimpl (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
  have p0079 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv x) (synCnnc)) p0077 p0078
  have p0081 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (.classMem (.cv x) (synCnnc)) (.classMem (.cv x) (synCvv)) p0079 p0007
  have p0083 := @gSimpr (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
  have p0084 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv y) (synCnnc)) p0077 p0083
  have p0086 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCvv)) p0084 p0032
  have p0087 :=
    @gJca
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)) p0081 p0086
  have p0089 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
      (synWb (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (.classMem (synCopk (.cv x) (.cv y)) (synClefin)))
      p0087 p0035
  have p0090 :=
    @gMpbid
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin)) p0076 p0089
  have p0092 :=
    @gSimpr (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
  have p0093 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)) p0074 p0092
  have p0104 :=
    @gJca
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv)) p0086 p0081
  have p0105 := @gKqlefinbr (.cv y) (.cv x) (synCvv) (synCvv)
  have p0106 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv)))
      (synWb (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
        (.classMem (synCopk (.cv y) (.cv x)) (synClefin)))
      p0104 p0105
  have p0107 :=
    @gMpbid
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
      (.classMem (synCopk (.cv y) (.cv x)) (synClefin)) p0093 p0106
  have p0108 :=
    @gJca
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
      (.classMem (synCopk (.cv y) (.cv x)) (synClefin)) p0090 p0107
  have p0110 := @gLefinantinn (.cv x) (.cv y)
  have p0111 :=
    @gSyl
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.imp (synWa (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
          (.classMem (synCopk (.cv y) (.cv x)) (synClefin))) (.classEq (.cv x) (.cv y)))
      p0077 p0110
  have p0112 :=
    @gMpd
      (synW3a synWtru (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
        (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
          (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))))
      (synWa (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
        (.classMem (synCopk (.cv y) (.cv x)) (synClefin)))
      (.classEq (.cv x) (.cv y)) p0108 p0111
  have p0113 :=
    @gSimp2 synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
  have p0114 :=
    @gSimp3 synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
  have p0115 :=
    @gJca
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)) p0113 p0114
  have p0116 := @gLefinconnexnn (.cv x) (.cv y)
  have p0117 :=
    @gSyl
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWo (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
        (.classMem (synCopk (.cv y) (.cv x)) (synClefin)))
      p0115 p0116
  have p0120 :=
    @gSyl
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv x) (synCnnc)) (.classMem (.cv x) (synCvv)) p0113 p0007
  have p0123 :=
    @gSyl
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv y) (synCvv)) p0114 p0032
  have p0124 :=
    @gJca
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)) p0120 p0123
  have p0126 :=
    @gSyl
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
      (synWb (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (.classMem (synCopk (.cv x) (.cv y)) (synClefin)))
      p0124 p0035
  have p0127 :=
    @gBiimprd
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin)) p0126
  have p0128 :=
    @gOrc (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
  have p0129 :=
    @gSyl6
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
      (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
      p0127 p0128
  have p0136 :=
    @gJca
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv)) p0123 p0120
  have p0138 :=
    @gSyl
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv)))
      (synWb (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
        (.classMem (synCopk (.cv y) (.cv x)) (synClefin)))
      p0136 p0105
  have p0139 :=
    @gBiimprd
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
      (.classMem (synCopk (.cv y) (.cv x)) (synClefin)) p0138
  have p0140 :=
    @gOlc (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
      (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
  have p0141 :=
    @gSyl6
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (synCopk (.cv y) (.cv x)) (synClefin))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x))
      (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
      p0139 p0140
  have p0142 :=
    @gJaod
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
      (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
      (.classMem (synCopk (.cv y) (.cv x)) (synClefin)) p0129 p0141
  have p0143 :=
    @gMpd
      (synW3a synWtru (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWo (.classMem (synCopk (.cv x) (.cv y)) (synClefin))
        (.classMem (synCopk (.cv y) (.cv x)) (synClefin)))
      (synWo (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))
      p0117 p0142
  have p0144_e04_recanon :
    Nominal.NPrf
      (.imp (synW3a synWtru
          (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
          (synWa (synWbr (.cv x) (synCkqrel (synClefin)) (.cv y))
            (synWbr (.cv y) (synCkqrel (synClefin)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWtru
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0112
  have p0144 :=
    @gSod synWtru x y z (synCnnc) (synCkqrel (synClefin)) (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      p0003 p0005 p0020 p0073 p0144_e04_recanon p0143
  have p0145 := Nominal.mp p0000 p0144
  exact p0145


end NFChoice.DirectNominalPrf.WPPReplay

end
