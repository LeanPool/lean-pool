/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecutreledgedecode`. -/
@[expose]
noncomputable def gHncodecutreledgedecode (x : Var) (v : Var) (u : Var) (A : Class)
    (C : Class) (_dv_A_C : Disjoint A.fv C.fv) (dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_C_u : u ∉ C.fv) (_dv_C_v : v ∉ C.fv) (dv_C_x : x ∉ C.fv)
    (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (synWbr C (synChncodecutrel A) (.cv v)) (synWrex u (synChwcn A)
          (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x))) (.classEq (.cv v) (.cv u)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ C.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have fresh_p_ne_v : p ≠ v := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_p : u ≠ p := Ne.symm fresh_p_ne_u
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ ((synCop C (.cv v))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_C, fresh_p_ne_v, or_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((synChncodecutinputs A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
          fresh_p_not_A, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((synChncodecutpairfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0007 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0008 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0009 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0010 :
    x ∉
      ((synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, dv_A_x, dv_C_x, (Ne.symm dv_v_x),
          (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    u ∉
      ((synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_p, dv_A_u, dv_C_u, dv_u_v,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x))) (.classEq (.cv v) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u,
          fresh_p_not_C, fresh_p_ne_x, fresh_p_ne_v, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (synWbr C (synChncodecutrel A) (.cv v)))
  have p0001 :=
    @gBiimpi (synWbr C (synChncodecutrel A) (.cv v))
      (.classMem (synCop C (.cv v)) (synChncodecutrel A)) p0000
  have p0002 := (Nominal.classEqRefl (synChncodecutrel A))
  have p0003 :=
    @gEleq2i (synChncodecutrel A)
      (synCima (synChncodecutpairfn) (synChncodecutinputs A)) (synCop C (.cv v)) p0002
  have p0004 :=
    @gSylib (synWbr C (synChncodecutrel A) (.cv v))
      (.classMem (synCop C (.cv v)) (synChncodecutrel A))
      (.classMem (synCop C (.cv v)) (synCima (synChncodecutpairfn) (synChncodecutinputs A)))
      p0001 p0003
  have p0005 := @gHncodecutpairfnfn
  have p0006 := @gFnfun (synCvv) (synChncodecutpairfn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gFvelima p (synCop C (.cv v)) (synChncodecutinputs A) (synChncodecutpairfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @gMpan (synWfun (synChncodecutpairfn))
      (.classMem (synCop C (.cv v)) (synCima (synChncodecutpairfn) (synChncodecutinputs A)))
      (synWrex p (synChncodecutinputs A)
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      p0007 p0008
  have p0010 :=
    @gSyl (synWbr C (synChncodecutrel A) (.cv v))
      (.classMem (synCop C (.cv v)) (synCima (synChncodecutpairfn) (synChncodecutinputs A)))
      (synWrex p (synChncodecutinputs A)
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      p0004 p0009
  have p0011 :=
    @gSimpl (.classMem (.cv p) (synChncodecutinputs A))
      (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v)))
  have p0012 :=
    @gHncodecutinputdecode x u A p dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0013 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChncodecutinputs A))
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (.classMem (.cv p) (synChncodecutinputs A))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u))
          (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))
      p0011 p0012
  have p0014 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))
  have p0015 :=
    @gFveq2d
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (.cv p) (synCop (.cv u) (synCsn (.cv x))) (synChncodecutpairfn) p0014
  have p0016 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))
  have p0017 :=
    @gSimpr
      (synWa (.classMem (.cv p) (synChncodecutinputs A))
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (.classMem (.cv u) (synChwcn A))
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0016 p0017
  have p0019 := @gHncodecutpairfnvalhwcn x u A dv_cache_0005
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (synCfv (synChncodecutpairfn) (synCop (.cv u) (synCsn (.cv x)))) (synCop
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (.cv u)))
      p0018 p0019
  have p0021 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synCfv (synChncodecutpairfn) (.cv p))
      (synCfv (synChncodecutpairfn) (synCop (.cv u) (synCsn (.cv x))))
      (synCop (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (.cv u))
      p0015 p0020
  have p0022 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synCfv (synChncodecutpairfn) (.cv p))
      (synCop (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (.cv u))
      p0021
  have p0024 :=
    @gSimpl
      (synWa (.classMem (.cv p) (synChncodecutinputs A))
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (.classMem (.cv u) (synChwcn A))
  have p0025 :=
    @gSimpr (.classMem (.cv p) (synChncodecutinputs A))
      (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v)))
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (synWa (.classMem (.cv p) (synChncodecutinputs A))
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))) p0024 p0025
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))) p0016 p0026
  have p0028 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synCop (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (.cv u))
      (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v)) p0022 p0027
  have p0029 :=
    @gOpth
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (.cv u) C (.cv v)
  have p0030 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (.classEq (synCop
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (.cv u)) (synCop C (.cv v)))
      (synWa (.classEq
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)) C)
        (.classEq (.cv u) (.cv v)))
      p0028 p0029
  have p0031 :=
    @gSimpl
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) C)
      (.classEq (.cv u) (.cv v))
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synWa (.classEq
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)) C)
        (.classEq (.cv u) (.cv v)))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) C)
      p0030 p0031
  have p0033 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      C p0032
  have p0051 :=
    @gSimpr
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) C)
      (.classEq (.cv u) (.cv v))
  have p0052 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synWa (.classEq
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)) C)
        (.classEq (.cv u) (.cv v)))
      (.classEq (.cv u) (.cv v)) p0030 p0051
  have p0053 :=
    @gEqcomd
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (.cv u) (.cv v) p0052
  have p0054 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
            (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
          (.classMem (.cv u) (synChwcn A)))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)))
      (.classEq (.cv v) (.cv u)) p0033 p0053
  have p0055 :=
    @gEx
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      p0054
  have p0056 :=
    @gReximdv
      (synWa (synWa (.classMem (.cv p) (synChncodecutinputs A))
          (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
        (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      x (synCfv (synC2nd) (.cv u)) dv_cache_0010 p0055
  have p0057 :=
    @gReximdva
      (synWa (.classMem (.cv p) (synChncodecutinputs A))
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (synWrex x (synCfv (synC2nd) (.cv u))
        (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x)))))
      (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      u (synChwcn A) dv_cache_0011 p0056
  have p0058 :=
    @gMpd
      (synWa (.classMem (.cv p) (synChncodecutinputs A))
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u))
          (.classEq (.cv p) (synCop (.cv u) (synCsn (.cv x))))))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p0013 p0057
  have p0059 :=
    @gEx (.classMem (.cv p) (synChncodecutinputs A))
      (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v)))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p0058
  have p0060 :=
    @gRexlimiv (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v)))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p (synChncodecutinputs A) dv_cache_0012 p0059
  have p0061 :=
    @gSyl (synWbr C (synChncodecutrel A) (.cv v))
      (synWrex p (synChncodecutinputs A)
        (.classEq (synCfv (synChncodecutpairfn) (.cv p)) (synCop C (.cv v))))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p0010 p0060
  exact p0061

/-- Checked nominal proof certificate identified upstream as `g_hncodecutfnvalhwcn`. -/
@[expose]
noncomputable def gHncodecutfnvalhwcn (x : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classEq (synCfv (synChncodecutfn) (synCop (.cv u) (synCsn (.cv x))))
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)))) :=
  by
  have p0000 := @gHwcnpair u A
  have p0001 :=
    @gOpeq1d (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synCsn (.cv x)) p0000
  have p0002 :=
    @gFveq2d (.classMem (.cv u) (synChwcn A)) (synCop (.cv u) (synCsn (.cv x)))
      (synCop (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synCsn (.cv x)))
      (synChncodecutfn) p0001
  have p0003 := @gFvex (.cv u) (synC1st)
  have p0004 := @gFvex (.cv u) (synC2nd)
  have p0005 :=
    @gHncodecutfnval x (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) p0003
      p0004
  have p0006 :=
    @gA1i
      (.classEq (synCfv (synChncodecutfn)
          (synCop (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
            (synCsn (.cv x))))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (.classMem (.cv u) (synChwcn A)) p0005
  have p0007 :=
    @gEqtrd (.classMem (.cv u) (synChwcn A))
      (synCfv (synChncodecutfn) (synCop (.cv u) (synCsn (.cv x))))
      (synCfv (synChncodecutfn)
        (synCop (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
          (synCsn (.cv x))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hncodecutreledgedecodetarget`. -/
@[expose]
noncomputable def gHncodecutreledgedecodetarget (x : Var) (v : Var) (A : Class)
    (C : Class) (dv_A_C : Disjoint A.fv C.fv) (dv_A_v : v ∉ A.fv) (_dv_A_x : x ∉ A.fv)
    (dv_C_v : v ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (synWbr C (synChncodecutrel A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ A.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have dv_cache_0001 : Disjoint (A).fv (C).fv := by
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0005 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0006 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_v, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0010 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0011 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv v)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ v from (by exact Ne.symm dv_v_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((synCfv (synC2nd) (.cv v))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    x ∉
      ((Wff.classEq C (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv z)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_C_x, fresh_x_ne_z, (Ne.symm dv_v_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    z ∉
      ((synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_v, fresh_z_not_C,
          fresh_z_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (.cv u) (synChwcn A))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0017 :
    u ∉
      ((synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_C,
          fresh_u_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gHncodecutreledgedecode z v u A C dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0001 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
  have p0002 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv u))) p0001 p0002
  have p0004 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
  have p0005 :=
    @gSimpr
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv z)))
      (.classEq (.cv v) (.cv u))
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (.classEq (.cv v) (.cv u)) p0004 p0005
  have p0007 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv v) (.cv u) p0006
  have p0008 :=
    @gFveq2d
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv u) (.cv v) (synC2nd) p0007
  have p0009 :=
    @gEleqtrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv z) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) p0003 p0008
  have p0011 :=
    @gSimpl
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv z)))
      (.classEq (.cv v) (.cv u))
  have p0012 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv z)))
      p0004 p0011
  have p0014 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A)) p0001 p0014
  have p0016 := @gHncodecutfnvalhwcn z u A dv_cache_0002
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (synCfv (synChncodecutfn) (synCop (.cv u) (synCsn (.cv z))))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
      p0015 p0016
  have p0018 :=
    @gEqcomd
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synCfv (synChncodecutfn) (synCop (.cv u) (synCsn (.cv z))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))
      p0017
  have p0023 :=
    @gOpeq1d
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv u) (.cv v) (synCsn (.cv z)) p0007
  have p0024 :=
    @gFveq2d
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synCop (.cv u) (synCsn (.cv z))) (synCop (.cv v) (synCsn (.cv z)))
      (synChncodecutfn) p0023
  have p0031 :=
    @gEqeltrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv v) (.cv u) (synChwcn A) p0006 p0015
  have p0032 := @gHncodecutfnvalhwcn z v A dv_cache_0003
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv z))))
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      p0031 p0032
  have p0034 :=
    @gN3eqtrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))
      (synCfv (synChncodecutfn) (synCop (.cv u) (synCsn (.cv z))))
      (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv z))))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      p0018 p0024 p0033
  have p0035 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      C
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      p0012 p0034
  have p0036 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv z)))
      p0009 p0035
  have p0037 :=
    @gHnwcutcodeeq3 (.cv x) (.cv z) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv v)) dv_cache_0011
  have p0038 :=
    @gEqeq2d (.classEq (.cv x) (.cv z))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      C p0037
  have p0039 :=
    @gRspcev
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)))
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv z)))
      x (.cv z) (synCfv (synC2nd) (.cv v)) dv_cache_0012 dv_cache_0013 dv_cache_0014
      p0038
  have p0040 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv v))) (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0036 p0039
  have p0041 :=
    @gEx
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0040
  have p0042 :=
    @gRexlimdva (.classMem (.cv u) (synChwcn A))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      z (synCfv (synC2nd) (.cv u)) dv_cache_0015 dv_cache_0016 p0041
  have p0043 :=
    @gRexlimiv
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      u (synChwcn A) dv_cache_0017 p0042
  have p0044 :=
    @gSyl (synWbr C (synChncodecutrel A) (.cv v))
      (synWrex u (synChwcn A) (synWrex z (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv z))) (.classEq (.cv v) (.cv u)))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0000 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_hncodecutreledgeihwcn`. -/
@[expose]
noncomputable def gHncodecutreledgeihwcn (x : Var) (v : Var) (A : Class)
    (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChncodecutrel A) (.cv v))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv ((synCfv (synC1st) (.cv v))).fv := by
    exact
      (show Disjoint (A).fv ((synCfv (synC1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv v)).fv) ∪ (((synC1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show v ∉ (A).fv from (by exact dv_A_v)))))),
                  (show Disjoint ((A).fv) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
  have p0001 := @gHwcnpair v A
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0000 p0001
  have p0004 :=
    @gEqeltrrd
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
      (synChwcn A) p0002 p0000
  have p0005 :=
    @gSimpr (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
  have p0006 :=
    @gJca
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classMem (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
        (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0004 p0005
  have p0007 := @gFvex (.cv v) (synC1st)
  have p0008 := @gFvex (.cv v) (synC2nd)
  have p0009 :=
    @gHncodecutreledgei x A (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) (.cv v))
      dv_cache_0001 p0007 p0008
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)))
          (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChncodecutrel A)
        (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0006 p0009
  have p0014 :=
    @gEqcomd
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))) p0002
  have p0015 :=
    @gBreq2d
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))) (.cv v)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChncodecutrel A) p0014
  have p0016 :=
    @gMpbid
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChncodecutrel A)
        (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChncodecutrel A) (.cv v))
      p0010 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsetstrictcutsemdv`. -/
@[expose]
noncomputable def gHncodecmpsetstrictcutsemdv (x : Var) (v : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (synChwcn A))
        (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
            (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let c : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_v : c ≠ v := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_c : v ≠ c := Ne.symm fresh_c_ne_v
  have fresh_c_ne_u : c ≠ u := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_c : u ≠ c := Ne.symm fresh_c_ne_u
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_c_ne_z : c ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_c : z ≠ c := Ne.symm fresh_c_ne_z
  have dv_cache_0001 : c ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0002 : u ≠ c := by
    clear dv_cache_0001
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0003 : v ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ c from (by exact fresh_v_ne_c))
  have dv_cache_0004 : Disjoint (A).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0005 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_c, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_c, not_false_eq_true])
  have dv_cache_0009 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0010 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv v)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ v from (by exact Ne.symm dv_v_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0011 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synCfv (synC2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv z)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), fresh_x_ne_z, (Ne.symm dv_v_x), dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_v, fresh_z_ne_u,
          fresh_z_ne_x, fresh_z_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0015 : z ∉ ((synWbr (.cv u) (synChwniso A) (.cv c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_c, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    c ∉
      ((synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_v, fresh_c_ne_u,
          fresh_c_ne_x, fresh_c_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 :
    c ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    c ∉
      ((synWa (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
          (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)) (synChncodecutrel A) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
          Finset.mem_union, Finset.mem_singleton, fresh_c_ne_u, fresh_c_ne_x,
          fresh_c_ne_v, fresh_c_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    c ∉
      ((synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_v, fresh_c_not_A, fresh_c_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    x ∉
      ((synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
            (synWbr (.cv c) (synChncodecutrel A) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_u_x),
          fresh_x_ne_c, dv_A_x, (Ne.symm dv_v_x), or_false, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Wff.classMem (.cv v) (synChwcn A))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, or_false, not_false_eq_true])
  have p0000 := @gBrhncodecmpset c v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gA1i
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex c
            (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
              (synWbr (.cv c) (synChncodecutrel A) (.cv v))))))
      (.classMem (.cv v) (synChwcn A)) p0000
  have p0002 :=
    @gHncodecutreledgedecodetarget z v A (.cv c) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0003 :=
    @gSimpl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
  have p0004 :=
    @gSimpr (synWbr (.cv u) (synChwniso A) (.cv c))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))
  have p0005 :=
    @gSyl
      (synWa (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv v))) p0003 p0004
  have p0007 :=
    @gSimpl (synWbr (.cv u) (synChwniso A) (.cv c))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))
  have p0008 :=
    @gSyl
      (synWa (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv v))))
      (synWbr (.cv u) (synChwniso A) (.cv c)) p0003 p0007
  have p0009 :=
    @gSimpr
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
  have p0010 :=
    @gBreq2d
      (synWa (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (.cv c)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      (.cv u) (synChwniso A) p0009
  have p0011 :=
    @gMpbid
      (synWa (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      p0008 p0010
  have p0012 :=
    @gJca
      (synWa (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      p0005 p0011
  have p0013 :=
    @gHnwcutcodeeq3 (.cv x) (.cv z) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv v)) dv_cache_0010
  have p0014 :=
    @gBreq2d (.classEq (.cv x) (.cv z))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      (.cv u) (synChwniso A) p0013
  have p0015 :=
    @gRspcev
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      x (.cv z) (synCfv (synC2nd) (.cv v)) dv_cache_0011 dv_cache_0012 dv_cache_0013
      p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (.classMem (.cv z) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWa (.classMem (.cv z) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0012 p0015
  have p0017 :=
    @gEx
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0016
  have p0018 :=
    @gRexlimdva (synWbr (.cv u) (synChwniso A) (.cv c))
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      z (synCfv (synC2nd) (.cv v)) dv_cache_0014 dv_cache_0015 p0017
  have p0019 :=
    @gSyl5 (synWbr (.cv c) (synChncodecutrel A) (.cv v))
      (synWrex z (synCfv (synC2nd) (.cv v)) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0002 p0018
  have p0020 :=
    @gImp (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWbr (.cv c) (synChncodecutrel A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0019
  have p0021 :=
    @gExlimiv
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      c dv_cache_0016 p0020
  have p0022 :=
    @gA1i
      (.imp (synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
            (synWbr (.cv c) (synChncodecutrel A) (.cv v))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (synChwcn A)) p0021
  have p0023 :=
    @gSimpr
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0024 :=
    @gSimpl
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0025 := @gHncodecutreledgeihwcn x v A dv_cache_0005
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChncodecutrel A) (.cv v))
      p0024 p0025
  have p0027 :=
    @gJca
      (synWa (synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChncodecutrel A) (.cv v))
      p0023 p0026
  have p0028 :=
    @gEx
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv x)) (synChncodecutrel A) (.cv v)))
      p0027
  have p0029 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
  have p0030 := @gHncodecutfnvalhwcn x v A dv_cache_0005
  have p0031 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0029 p0030
  have p0032 := @gFvex (synCop (.cv v) (synCsn (.cv x))) (synChncodecutfn)
  have p0033 :=
    @gA1i
      (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x)))) (synCvv))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      p0032
  have p0034 :=
    @gEqeltrrd
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synCvv) p0031 p0033
  have p0035 :=
    @gSimpr
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0036 :=
    @gId
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0037 :=
    @gBreq2d
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (.cv c)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (.cv u) (synChwniso A) p0036
  have p0039 :=
    @gBreq1d
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (.cv c)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (.cv v) (synChncodecutrel A) p0036
  have p0040 :=
    @gAnbi12d
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr (.cv c) (synChncodecutrel A) (.cv v))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChncodecutrel A) (.cv v))
      p0037 p0039
  have p0041 :=
    @gSyl
      (synWa (synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classEq (.cv c)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWb (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (synWbr (.cv c) (synChncodecutrel A) (.cv v))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
          (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)) (synChncodecutrel A) (.cv v))))
      p0035 p0040
  have p0042 :=
    @gBiimprd
      (synWa (synWa (.classMem (.cv v) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))) (.classEq (.cv c)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv x)) (synChncodecutrel A) (.cv v)))
      p0041
  have p0043 :=
    @gSpcimedv
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv x)) (synChncodecutrel A) (.cv v)))
      c
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synCvv) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0034 p0042
  have p0044 :=
    @gSyld
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv x)) (synChncodecutrel A) (.cv v)))
      (synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (synWbr (.cv c) (synChncodecutrel A) (.cv v))))
      p0028 p0043
  have p0045 :=
    @gRexlimdva (.classMem (.cv v) (synChwcn A))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (synWbr (.cv c) (synChncodecutrel A) (.cv v))))
      x (synCfv (synC2nd) (.cv v)) dv_cache_0020 dv_cache_0021 p0044
  have p0046 :=
    @gImpbid (.classMem (.cv v) (synChwcn A))
      (synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (synWbr (.cv c) (synChncodecutrel A) (.cv v))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0022 p0045
  have p0047 :=
    @gOrbi2d (.classMem (.cv v) (synChwcn A))
      (synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (synWbr (.cv c) (synChncodecutrel A) (.cv v))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0046
  have p0048 :=
    @gBitrd (.classMem (.cv v) (synChwcn A))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex c
          (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
            (synWbr (.cv c) (synChncodecutrel A) (.cv v)))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0001 p0047
  exact p0048

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsetrefndv`. -/
@[expose]
noncomputable def gHncodecmpsetrefndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (synWbr (synChncodecmpset A) (synCref) (synChwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
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
  have dv_cache_0003 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0004 : u ∉ ((synChwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((synChncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gHncodecmpsetexg A
  have p0001 := @gHwcnexg A
  have p0002 := @gSimpr (.classMem A (synCvv)) (.classMem (.cv u) (synChwcn A))
  have p0003 := @gHwnisorefli u A dv_cache_0001
  have p0004 :=
    @gOrc (synWbr (.cv u) (synChwniso A) (.cv u))
      (synWrex x (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
  have p0005 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (synWbr (.cv u) (synChwniso A) (.cv u))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv u)) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0003 p0004
  have p0006 :=
    @gHncodecmpsetstrictcutsemdv x u u A dv_cache_0001 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0003
  have p0007 :=
    @gMpbird (.classMem (.cv u) (synChwcn A))
      (synWbr (.cv u) (synChncodecmpset A) (.cv u))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv u)) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0005 p0006
  have p0008 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) (synWbr (.cv u) (synChncodecmpset A) (.cv u))
      p0002 p0007
  have p0009 :=
    @gRefrd (.classMem A (synCvv)) u (synChwcn A) (synChncodecmpset A) (synCvv)
      (synCvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0000 p0001 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hncodecutreltargetclndv`. -/
@[expose]
noncomputable def gHncodecutreltargetclndv (v : Var) (A : Class) (C : Class)
    (dv_A_C : Disjoint A.fv C.fv) (dv_A_v : v ∉ A.fv) (dv_C_v : v ∉ C.fv) :
    Nominal.NPrf
      (.imp (synWbr C (synChncodecutrel A) (.cv v)) (.classMem (.cv v) (synChwcn A))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ A.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : Disjoint (A).fv (C).fv := by
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0006 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_v, not_false_eq_true])
  have dv_cache_0007 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0010 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0011 : x ∉ ((Wff.classMem (.cv v) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv u) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((Wff.classMem (.cv v) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @gHncodecutreledgedecode x v u A C dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0001 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
  have p0002 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A)) p0001 p0002
  have p0004 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
  have p0005 :=
    @gSimpr
      (.classEq C (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)))
      (.classEq (.cv v) (.cv u))
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      (.classEq (.cv v) (.cv u)) p0004 p0005
  have p0007 :=
    @gEleq1d
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (.cv v) (.cv u) (synChwcn A) p0006
  have p0008 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0003 p0007
  have p0009 :=
    @gExp31 (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      (.classMem (.cv v) (synChwcn A)) p0008
  have p0010 :=
    @gImp (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.imp (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))) (.classMem (.cv v) (synChwcn A)))
      p0009
  have p0011 :=
    @gRexlimdva (.classMem (.cv u) (synChwcn A))
      (synWa (.classEq C
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      (.classMem (.cv v) (synChwcn A)) x (synCfv (synC2nd) (.cv u)) dv_cache_0011
      dv_cache_0012 p0010
  have p0012 :=
    @gRexlimiv
      (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv v) (synChwcn A)) u (synChwcn A) dv_cache_0013 p0011
  have p0013 :=
    @gSyl (synWbr C (synChncodecutrel A) (.cv v))
      (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u)) (synWa (.classEq C
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      (.classMem (.cv v) (synChwcn A)) p0000 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsetssxpndv`. -/
@[expose]
noncomputable def gHncodecmpsetssxpndv (A : Class) :
    Nominal.NPrf (synWss (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_c : u ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_u : c ≠ u := Ne.symm fresh_u_ne_c
  have fresh_v_ne_c : v ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_v : c ≠ v := Ne.symm fresh_v_ne_c
  have dv_cache_0001 : c ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0002 : u ≠ c := by
    clear dv_cache_0001
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0003 : v ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ c from (by exact fresh_v_ne_c))
  have dv_cache_0004 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : Disjoint (A).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (A).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0006 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_c, not_false_eq_true])
  have dv_cache_0008 :
    c ∉
      ((synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_u, fresh_c_not_A, fresh_c_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0009 : u ∉ ((synChncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0010 : v ∉ ((synChncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((synCxp (synChwcn A) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_u_not_A, or_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((synCxp (synChwcn A) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_v_not_A, or_false, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (synWbr (.cv u) (synChncodecmpset A) (.cv v)))
  have p0001 :=
    @gBiimpri (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synChncodecmpset A)) p0000
  have p0002 := @gBrhncodecmpset c v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @gBiimpi (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex c
          (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
            (synWbr (.cv c) (synChncodecutrel A) (.cv v)))))
      p0002
  have p0004 := @gHwnisohwisob v u A dv_cache_0004
  have p0005 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0004
  have p0006 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0007 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0005
      p0006
  have p0008 :=
    @gSimpl (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWbr (.cv c) (synChncodecutrel A) (.cv v))
  have p0009 := @gHwnisohwisob c u A dv_cache_0002
  have p0010 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv c) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv c)))
      p0009
  have p0011 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv c) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv c))
  have p0012 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv c) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv c)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv c) (synChwcn A))) p0010
      p0011
  have p0013 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv c) (synChwcn A))
  have p0014 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv c) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0012 p0013
  have p0015 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv c)) (.classMem (.cv u) (synChwcn A)) p0008
      p0014
  have p0016 :=
    @gSimpr (synWbr (.cv u) (synChwniso A) (.cv c))
      (synWbr (.cv c) (synChncodecutrel A) (.cv v))
  have p0017 :=
    @gHncodecutreltargetclndv v A (.cv c) dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0018 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (synWbr (.cv c) (synChncodecutrel A) (.cv v)) (.classMem (.cv v) (synChwcn A))
      p0016 p0017
  have p0019 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0015 p0018
  have p0020 :=
    @gExlimiv
      (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
        (synWbr (.cv c) (synChncodecutrel A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) c
      dv_cache_0008 p0019
  have p0021 :=
    @gJaoi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWex c (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
          (synWbr (.cv c) (synChncodecutrel A) (.cv v))))
      p0007 p0020
  have p0022 :=
    @gSyl (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWex c
          (synWa (synWbr (.cv u) (synChwniso A) (.cv c))
            (synWbr (.cv c) (synChncodecutrel A) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0003
      p0021
  have p0023 := @gOpelxp (.cv u) (.cv v) (synChwcn A) (synChwcn A)
  have p0024 :=
    @gBiimpri (.classMem (synCop (.cv u) (.cv v)) (synCxp (synChwcn A) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0023
  have p0025 :=
    @gSyl (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (synCop (.cv u) (.cv v)) (synCxp (synChwcn A) (synChwcn A))) p0022
      p0024
  have p0026 :=
    @gSyl (.classMem (synCop (.cv u) (.cv v)) (synChncodecmpset A))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synCxp (synChwcn A) (synChwcn A))) p0001
      p0025
  have p0027 :=
    @gRelssi u v (synChncodecmpset A) (synCxp (synChwcn A) (synChwcn A))
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpdefaultcnndv`. -/
@[expose]
noncomputable def gHncodecmpdefaultcnndv (A : Class) :
    Nominal.NPrf
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A)) :=
  by
  have dv_cache_0001 :
    Disjoint (A).fv
      ((synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))).fv :=
    by
    exact
      (show Disjoint (A).fv ((synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))).fv
        from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
          exact
            (show
              Disjoint ((A).fv)
                ((((synCkqrel (synClefin))).fv) ∪ (((synCxp (synC0) (synC0))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((synCkqrel (synClefin))).fv) from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel];
                      exact
                        (show Disjoint ((A).fv) (((synClefin)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
                            exact
                              (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint ((A).fv) (((synCxp (synC0) (synC0))).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp];
                      exact
                        (show Disjoint ((A).fv) ((((synC0)).fv) ∪ (((synC0)).fv)) from
                          (Finset.disjoint_union_right.mpr
                            ⟨(show Disjoint ((A).fv) (((synC0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp)))),
                              (show Disjoint ((A).fv) (((synC0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp))))⟩))))⟩))))
  have p0000 := @gWecomparisondefaultemptywe
  have p0001 := @gN0ss A
  have p0002 :=
    @gPm32i
      (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
        (synC0))
      (synWss (synC0) A) p0000 p0001
  have p0004 :=
    @gBrex (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      (synCwe)
  have p0005 := Nominal.mp p0000 p0004
  have p0006 :=
    @gSimpli
      (.classMem (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCvv))
      (.classMem (synC0) (synCvv)) p0005
  have p0010 :=
    @gSimpri
      (.classMem (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCvv))
      (.classMem (synC0) (synCvv)) p0005
  have p0011 :=
    @gElhwcodes A (synC0)
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) dv_cache_0001 p0006
      p0010
  have p0012 :=
    @gBiimpri
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcodes A))
      (synWa (synWbr (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synCwe)
          (synC0)) (synWss (synC0) A))
      p0011
  have p0013 := Nominal.mp p0002 p0012
  have p0014 := @gInss2 (synCkqrel (synClefin)) (synCxp (synC0) (synC0))
  have p0023 :=
    @gOpfv1st (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      p0006 p0010
  have p0032 :=
    @gOpfv2nd (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)
      p0006 p0010
  have p0042 :=
    @gXpeq12i
      (synCfv (synC2nd)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC0)
      (synCfv (synC2nd)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synC0) p0032 p0032
  have p0043 :=
    @gSseq12i
      (synCfv (synC1st)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
      (synCxp (synCfv (synC2nd)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCfv (synC2nd)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCxp (synC0) (synC0)) p0023 p0042
  have p0044 :=
    @gBiimpri
      (synWss (synCfv (synC1st)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWss (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
        (synCxp (synC0) (synC0)))
      p0043
  have p0045 := Nominal.mp p0014 p0044
  have p0046 :=
    @gPm32i
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcodes A))
      (synWss (synCfv (synC1st)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synCxp (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synCfv (synC2nd)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0013 p0045
  have p0055 :=
    @gOpex (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0) p0006
      p0010
  have p0056 :=
    @gElhwcncl A
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
  have p0057 := Nominal.mp p0055 p0056
  have p0058 :=
    @gBiimpri
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (synWa (.classMem
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
          (synChwcodes A)) (synWss (synCfv (synC1st)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synCxp (synCfv (synC2nd)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synCfv (synC2nd)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      p0057
  have p0059 := Nominal.mp p0046 p0058
  exact p0059

/-- Checked nominal proof certificate identified upstream as `g_hwcnweclndv`. -/
@[expose]
noncomputable def gHwcnweclndv (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synChwcn A))
        (synWbr (synCfv (synC1st) B) (synCwe) (synCfv (synC2nd) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (.classMem B (synChwcn A))
          (synWbr (synCfv (synC1st) B) (synCwe) (synCfv (synC2nd) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classMem B (synChwcn A))
  have p0001 := @gElex B (synChwcn A)
  have p0002 := @gId (.classEq (.cv u) B)
  have p0003 := @gEleq1d (.classEq (.cv u) B) (.cv u) B (synChwcn A) p0002
  have p0005 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC1st) p0002
  have p0007 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC2nd) p0002
  have p0008 :=
    @gBreq12d (.classEq (.cv u) B) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) B)
      (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B) (synCwe) p0005 p0007
  have p0009 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWbr (synCfv (synC1st) B) (synCwe) (synCfv (synC2nd) B)) p0003 p0008
  have p0010 := @gHwcnwendv u A dv_cache_0001
  have p0011 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))))
      (.imp (.classMem B (synChwcn A))
        (synWbr (synCfv (synC1st) B) (synCwe) (synCfv (synC2nd) B)))
      u B (synCvv) dv_cache_0002 dv_cache_0003 p0009 p0010
  have p0012 :=
    @gSyl (.classMem B (synChwcn A)) (.classMem B (synCvv))
      (.imp (.classMem B (synChwcn A))
        (synWbr (synCfv (synC1st) B) (synCwe) (synCfv (synC2nd) B)))
      p0001 p0011
  have p0013 :=
    @gMpd (.classMem B (synChwcn A)) (.classMem B (synChwcn A))
      (synWbr (synCfv (synC1st) B) (synCwe) (synCfv (synC2nd) B)) p0000 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_hwcnbaseclndv`. -/
@[expose]
noncomputable def gHwcnbaseclndv (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B (synChwcn A)) (synWss (synCfv (synC2nd) B) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 :
    u ∉ ((Wff.imp (.classMem B (synChwcn A)) (synWss (synCfv (synC2nd) B) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gId (.classMem B (synChwcn A))
  have p0001 := @gElex B (synChwcn A)
  have p0002 := @gId (.classEq (.cv u) B)
  have p0003 := @gEleq1d (.classEq (.cv u) B) (.cv u) B (synChwcn A) p0002
  have p0005 := @gFveq2d (.classEq (.cv u) B) (.cv u) B (synC2nd) p0002
  have p0006 :=
    @gSseq1d (.classEq (.cv u) B) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) B) A
      p0005
  have p0007 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem (.cv u) (synChwcn A))
      (.classMem B (synChwcn A)) (synWss (synCfv (synC2nd) (.cv u)) A)
      (synWss (synCfv (synC2nd) B) A) p0003 p0006
  have p0008 := @gHwcnbase u A dv_cache_0001
  have p0009 :=
    @gVtoclg
      (.imp (.classMem (.cv u) (synChwcn A)) (synWss (synCfv (synC2nd) (.cv u)) A))
      (.imp (.classMem B (synChwcn A)) (synWss (synCfv (synC2nd) B) A)) u B (synCvv)
      dv_cache_0002 dv_cache_0003 p0007 p0008
  have p0010 :=
    @gSyl (.classMem B (synChwcn A)) (.classMem B (synCvv))
      (.imp (.classMem B (synChwcn A)) (synWss (synCfv (synC2nd) B) A)) p0001 p0009
  have p0011 :=
    @gMpd (.classMem B (synChwcn A)) (.classMem B (synChwcn A))
      (synWss (synCfv (synC2nd) B) A) p0000 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsetstrictcutsemclndv`. -/
@[expose]
noncomputable def gHncodecmpsetstrictcutsemclndv (x : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
        (synWb (synWbr B (synChncodecmpset A) C) (synWo (synWbr B (synChwniso A) C)
            (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : x ∉ ((synCfv (synC2nd) (.cv v))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCfv (synC2nd) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_C_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv v) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv u) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0008 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0009 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0010 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0011 :
    u ∉
      ((Wff.imp (.classMem (.cv v) (synChwcn A))
          (synWb (synWbr B (synChncodecmpset A) (.cv v))
            (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
                (synWbr B (synChwniso A) (synChnwcutcode (synCfv (synC1st) (.cv v))
                    (synCfv (synC2nd) (.cv v)) (.cv x)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_A,
          fresh_u_not_B, fresh_u_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0012 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0013 :
    v ∉
      ((Wff.imp (.classMem B (synCvv)) (.imp (.classMem C (synChwcn A))
            (synWb (synWbr B (synChncodecmpset A) C) (synWo (synWbr B (synChwniso A) C)
                (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
                    (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C)
                      (.cv x))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, fresh_v_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gSimpr (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0001 := @gSimpl (.classMem B (synChwcn A)) (.classMem C (synChwcn A))
  have p0002 := @gElex B (synChwcn A)
  have p0003 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synChwcn A)) (.classMem B (synCvv)) p0001 p0002
  have p0005 := @gElex C (synChwcn A)
  have p0006 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A)) (.classMem C (synCvv)) p0000 p0005
  have p0007 := @gId (.classEq (.cv v) C)
  have p0008 := @gEleq1d (.classEq (.cv v) C) (.cv v) C (synChwcn A) p0007
  have p0009 := @gEqid B
  have p0010 := @gA1i (.classEq B B) (.classEq (.cv v) C) p0009
  have p0012 :=
    @gBreq12d (.classEq (.cv v) C) B B (.cv v) C (synChncodecmpset A) p0010 p0007
  have p0016 := @gBreq12d (.classEq (.cv v) C) B B (.cv v) C (synChwniso A) p0010 p0007
  have p0018 := @gFveq2d (.classEq (.cv v) C) (.cv v) C (synC2nd) p0007
  have p0021 :=
    (Nominal.classEqRefl
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0022 :=
    @gA1i
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synCop (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (.cv v) C) p0021
  have p0024 := @gFveq2d (.classEq (.cv v) C) (.cv v) C (synC1st) p0007
  have p0029 :=
    @gDifeq1d (.classEq (.cv v) C) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C)
      (synCid) p0024
  have p0030 :=
    @gCnveqd (.classEq (.cv v) C) (synCdif (synCfv (synC1st) (.cv v)) (synCid))
      (synCdif (synCfv (synC1st) C) (synCid)) p0029
  have p0031 :=
    @gImaeq1d (.classEq (.cv v) C)
      (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
      (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x)) p0030
  have p0032 :=
    @gIneq12d (.classEq (.cv v) C) (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C)
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x)))
      p0018 p0031
  have p0041 :=
    @gXpeq12d (.classEq (.cv v) C)
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) C)
        (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) C)
        (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x))))
      p0032 p0032
  have p0042 :=
    @gIneq12d (.classEq (.cv v) C) (synCfv (synC1st) (.cv v)) (synCfv (synC1st) C)
      (synCxp (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      (synCxp (synCin (synCfv (synC2nd) C)
          (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x))))
        (synCin (synCfv (synC2nd) C)
          (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x)))))
      p0024 p0041
  have p0051 :=
    @gOpeq12d (.classEq (.cv v) C)
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC1st) C) (synCxp (synCin (synCfv (synC2nd) C)
            (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x))))
          (synCin (synCfv (synC2nd) C)
            (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) C)
        (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x))))
      p0042 p0032
  have p0052 :=
    (Nominal.classEqRefl
      (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)))
  have p0053 :=
    @gA1i
      (.classEq (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)) (synCop
          (synCin (synCfv (synC1st) C) (synCxp (synCin (synCfv (synC2nd) C)
                (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) C)
                (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
                  (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) C)
            (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (.cv v) C) p0052
  have p0054 :=
    @gEqcomd (.classEq (.cv v) C)
      (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))
      (synCop (synCin (synCfv (synC1st) C) (synCxp (synCin (synCfv (synC2nd) C)
              (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) C)
              (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) C)
          (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x)))))
      p0053
  have p0055 :=
    @gN3eqtrd (.classEq (.cv v) C)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synCop (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      (synCop (synCin (synCfv (synC1st) C) (synCxp (synCin (synCfv (synC2nd) C)
              (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) C)
              (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) C)
          (synCima (synCcnv (synCdif (synCfv (synC1st) C) (synCid))) (synCsn (.cv x)))))
      (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)) p0022 p0051
      p0054
  have p0056 :=
    @gBreq12d (.classEq (.cv v) C) B B
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))
      (synChwniso A) p0010 p0055
  have p0057 :=
    @gRexeqbidv (.classEq (.cv v) C)
      (synWbr B (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr B (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)))
      x (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) C) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0018 p0056
  have p0058 :=
    @gOrbi12d (.classEq (.cv v) C) (synWbr B (synChwniso A) (.cv v))
      (synWbr B (synChwniso A) C)
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr B (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))))
      p0016 p0057
  have p0059 :=
    @gBibi12d (.classEq (.cv v) C) (synWbr B (synChncodecmpset A) (.cv v))
      (synWbr B (synChncodecmpset A) C)
      (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr B (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWo (synWbr B (synChwniso A) C) (synWrex x (synCfv (synC2nd) C)
          (synWbr B (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)))))
      p0012 p0058
  have p0060 :=
    @gImbi12d (.classEq (.cv v) C) (.classMem (.cv v) (synChwcn A))
      (.classMem C (synChwcn A))
      (synWb (synWbr B (synChncodecmpset A) (.cv v))
        (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr B (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWb (synWbr B (synChncodecmpset A) C) (synWo (synWbr B (synChwniso A) C)
          (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))))))
      p0008 p0059
  have p0061 :=
    @gImbi2d (.classEq (.cv v) C)
      (.imp (.classMem (.cv v) (synChwcn A)) (synWb (synWbr B (synChncodecmpset A) (.cv v))
          (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
              (synWbr B (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x)))))))
      (.imp (.classMem C (synChwcn A)) (synWb (synWbr B (synChncodecmpset A) C)
          (synWo (synWbr B (synChwniso A) C) (synWrex x (synCfv (synC2nd) C)
              (synWbr B (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)))))))
      (.classMem B (synCvv)) p0060
  have p0062 := @gEqid (.cv v)
  have p0063 := @gA1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0062
  have p0064 := @gEleq1d (.classEq (.cv u) B) (.cv v) (.cv v) (synChwcn A) p0063
  have p0065 := @gId (.classEq (.cv u) B)
  have p0068 :=
    @gBreq12d (.classEq (.cv u) B) (.cv u) B (.cv v) (.cv v) (synChncodecmpset A) p0065
      p0063
  have p0072 :=
    @gBreq12d (.classEq (.cv u) B) (.cv u) B (.cv v) (.cv v) (synChwniso A) p0065 p0063
  have p0075 := @gFveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (synC2nd) p0063
  have p0078 :=
    @gA1i
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synCop (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x))))))
      (.classEq (.cv u) B) p0021
  have p0081 := @gFveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (synC1st) p0063
  have p0088 :=
    @gDifeq1d (.classEq (.cv u) B) (synCfv (synC1st) (.cv v))
      (synCfv (synC1st) (.cv v)) (synCid) p0081
  have p0089 :=
    @gCnveqd (.classEq (.cv u) B) (synCdif (synCfv (synC1st) (.cv v)) (synCid))
      (synCdif (synCfv (synC1st) (.cv v)) (synCid)) p0088
  have p0090 :=
    @gImaeq1d (.classEq (.cv u) B)
      (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
      (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCsn (.cv x)) p0089
  have p0091 :=
    @gIneq12d (.classEq (.cv u) B) (synCfv (synC2nd) (.cv v))
      (synCfv (synC2nd) (.cv v))
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid))) (synCsn (.cv x)))
      p0075 p0090
  have p0102 :=
    @gXpeq12d (.classEq (.cv u) B)
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      p0091 p0091
  have p0103 :=
    @gIneq12d (.classEq (.cv u) B) (synCfv (synC1st) (.cv v))
      (synCfv (synC1st) (.cv v))
      (synCxp (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      (synCxp (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      p0081 p0102
  have p0114 :=
    @gOpeq12d (.classEq (.cv u) B)
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv x))))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv x))))
      p0103 p0091
  have p0117 :=
    @gEqcomd (.classEq (.cv u) B)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synCop (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      p0078
  have p0118 :=
    @gN3eqtrd (.classEq (.cv u) B)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synCop (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      (synCop (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv x)))))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv x)))))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      p0078 p0114 p0117
  have p0119 :=
    @gBreq12d (.classEq (.cv u) B) (.cv u) B
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChwniso A) p0065 p0118
  have p0120 :=
    @gRexeqbidv (.classEq (.cv u) B)
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (synWbr B (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      x (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv v)) dv_cache_0001
      dv_cache_0001 dv_cache_0004 p0075 p0119
  have p0121 :=
    @gOrbi12d (.classEq (.cv u) B) (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr B (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr B (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0072 p0120
  have p0122 :=
    @gBibi12d (.classEq (.cv u) B) (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr B (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr B (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0068 p0121
  have p0123 :=
    @gImbi12d (.classEq (.cv u) B) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv v) (synChwcn A))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWb (synWbr B (synChncodecmpset A) (.cv v))
        (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
            (synWbr B (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0064 p0122
  have p0124 :=
    @gHncodecmpsetstrictcutsemdv x v u A dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009
  have p0125 :=
    @gVtoclg
      (.imp (.classMem (.cv v) (synChwcn A))
        (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
            (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x)))))))
      (.imp (.classMem (.cv v) (synChwcn A)) (synWb (synWbr B (synChncodecmpset A) (.cv v))
          (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
              (synWbr B (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x)))))))
      u B (synCvv) dv_cache_0010 dv_cache_0011 p0123 p0124
  have p0126 :=
    @gVtoclg
      (.imp (.classMem B (synCvv)) (.imp (.classMem (.cv v) (synChwcn A))
          (synWb (synWbr B (synChncodecmpset A) (.cv v))
            (synWo (synWbr B (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
                (synWbr B (synChwniso A) (synChnwcutcode (synCfv (synC1st) (.cv v))
                    (synCfv (synC2nd) (.cv v)) (.cv x))))))))
      (.imp (.classMem B (synCvv)) (.imp (.classMem C (synChwcn A))
          (synWb (synWbr B (synChncodecmpset A) C) (synWo (synWbr B (synChwniso A) C)
              (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
                  (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))))))))
      v C (synCvv) dv_cache_0012 dv_cache_0013 p0061 p0125
  have p0127 :=
    @gSyl (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synCvv))
      (.imp (.classMem B (synCvv)) (.imp (.classMem C (synChwcn A))
          (synWb (synWbr B (synChncodecmpset A) C) (synWo (synWbr B (synChwniso A) C)
              (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
                  (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))))))))
      p0006 p0126
  have p0128 :=
    @gMpd (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem B (synCvv))
      (.imp (.classMem C (synChwcn A)) (synWb (synWbr B (synChncodecmpset A) C)
          (synWo (synWbr B (synChwniso A) C) (synWrex x (synCfv (synC2nd) C)
              (synWbr B (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x)))))))
      p0003 p0127
  have p0129 :=
    @gMpd (synWa (.classMem B (synChwcn A)) (.classMem C (synChwcn A)))
      (.classMem C (synChwcn A))
      (synWb (synWbr B (synChncodecmpset A) C) (synWo (synWbr B (synChwniso A) C)
          (synWrex x (synCfv (synC2nd) C) (synWbr B (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) C) (synCfv (synC2nd) C) (.cv x))))))
      p0000 p0128
  exact p0129

/-- Checked nominal proof certificate identified upstream as `g_hncodetotalleftmemndv`. -/
@[expose]
noncomputable def gHncodetotalleftmemndv (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A)) :=
  by
  have p0000 := @gHncodecmpdefaultcnndv A
  have p0001 :=
    @gSimpr
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv u) (synChwcn A))
  have p0002 :=
    @gSimpl
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.neg (.classMem (.cv u) (synChwcn A)))
  have p0003 :=
    @gIfclda
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hncodetotalrightmemndv`. -/
@[expose]
noncomputable def gHncodetotalrightmemndv (v : Var) (A : Class) (_dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A)) :=
  by
  have p0000 := @gHncodecmpdefaultcnndv A
  have p0001 :=
    @gSimpr
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv v) (synChwcn A))
  have p0002 :=
    @gSimpl
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.neg (.classMem (.cv v) (synChwcn A)))
  have p0003 :=
    @gIfclda
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv v) (synChwcn A)) (.cv v)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hncodecomparisontotalndv`. -/
@[expose]
noncomputable def gHncodecomparisontotalndv (x : Var) (v : Var) (u : Var) (A : Class)
    (h : Var) (dv_A_h : h ∉ A.fv) (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_h_x : h ≠ x)
    (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (synW3o (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))))) (synWrex x (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWex h (synWiso (.cv h) (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCin (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                    (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)))) (synCid))) (synCsn (.cv x))))))
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x))))))) (synWrex x
          (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWex h (synWiso (.cv h) (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCin (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                    (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                                (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                                (synC0)))) (synCid))) (synCsn (.cv x))))))
              (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_u, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 :
    h ∉
      ((synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_v, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    h ∉
      ((synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_u, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    h ∉
      ((synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_v, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact dv_h_x))
  have p0000 := @gHncodecmpdefaultcnndv A
  have p0001 :=
    @gSimpr
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv u) (synChwcn A))
  have p0002 :=
    @gSimpl
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.neg (.classMem (.cv u) (synChwcn A)))
  have p0003 :=
    @gIfclda
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 :=
    @gHwcnweclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0006 := Nominal.mp p0004 p0005
  have p0008 :=
    @gSimpr
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv v) (synChwcn A))
  have p0009 :=
    @gSimpl
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.neg (.classMem (.cv v) (synChwcn A)))
  have p0010 :=
    @gIfclda
      (.classMem
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
        (synChwcn A))
      (.classMem (.cv v) (synChwcn A)) (.cv v)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
      (synChwcn A) p0008 p0009
  have p0011 := Nominal.mp p0000 p0010
  have p0012 :=
    @gHwcnweclndv A
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gWecomparisonterminalfdv x
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      h
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0006 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end
