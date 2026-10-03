/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001038Leaf1stReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001039SwapReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001040SsetReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001041CoReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001042ImaReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001043SiReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001044IdReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001045XpReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001046CnvReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001047FvReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001048Leaf2ndReflected001
public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_oddnn (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_coddfin)) (.classMem A (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wa (syn_wrex n (syn_cnnc)
            (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
          (syn_wne A (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classMem A (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_n_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_eqeq1 (.cv x) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A)
      (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc)
      dv_cache_0001 p0000
  have p0002 := @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A)
      (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n
      dv_cache_0002
  have p0005 :=
    @g_elab2g
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      x A (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_coddfin))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      p0005
  have p0007 := @g_nncaddccl (.cv n) (.cv n)
  have p0008 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0007
  have p0009 := @g_peano2 (syn_cplc (.cv n) (.cv n))
  have p0010 := @g_eleq1a (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cnnc) A
  have p0011 :=
    @g_n_3syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_cnnc))
      (.imp (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (.classMem A (syn_cnnc)))
      p0008 p0009 p0010
  have p0012 :=
    @g_rexlimiv (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classMem A (syn_cnnc)) n (syn_cnnc) dv_cache_0005 p0011
  have p0013 :=
    @g_adantr
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) p0012
  have p0014 :=
    @g_syl (.classMem A (syn_coddfin))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      (.classMem A (syn_cnnc)) p0006 p0013
  exact p0014

@[expose]
noncomputable def g_evennnul (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cevenfin)) (syn_wne A (syn_c0))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n))))
          (syn_wne A (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_eqeq1 (.cv x) A (syn_cplc (.cv n) (.cv n))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
      (.classEq A (syn_cplc (.cv n) (.cv n))) n (syn_cnnc) dv_cache_0001 p0000
  have p0002 := @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A)
      (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n
      dv_cache_0002
  have p0005 :=
    @g_elab2g
      (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n))))
        (syn_wne A (syn_c0)))
      x A (syn_cevenfin) (syn_cevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_cevenfin))
      (syn_wa (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n))))
        (syn_wne A (syn_c0)))
      p0005
  have p0007 :=
    @g_simprd (.classMem A (syn_cevenfin))
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (.cv n) (.cv n)))) (syn_wne A (syn_c0))
      p0006
  exact p0007

@[expose]
noncomputable def g_oddnnul (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_coddfin)) (syn_wne A (syn_c0))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wa (syn_wrex n (syn_cnnc)
            (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
          (syn_wne A (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_eqeq1 (.cv x) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A)
      (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc)
      dv_cache_0001 p0000
  have p0002 := @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A)
      (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n
      dv_cache_0002
  have p0005 :=
    @g_elab2g
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      x A (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_coddfin))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      p0005
  have p0007 :=
    @g_simprd (.classMem A (syn_coddfin))
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wne A (syn_c0)) p0006
  exact p0007

@[expose]
noncomputable def g_sucevenodd (A : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cevenfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
        (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin))) :=
  by
  let proofSupport : Finset Var := A.fv
  let m : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have dv_cache_0001 : m ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_x, fresh_m_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : m ≠ x := by
    clear dv_cache_0001
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m))))
          (syn_wne A (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_m,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((Wff.classEq (.cv x) (syn_cplc A (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_x, fresh_m_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cplc A (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    x ∉
      ((syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c))
              (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
          (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_m,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_eqeq1 (.cv x) A (syn_cplc (.cv m) (.cv m))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))
      (.classEq A (syn_cplc (.cv m) (.cv m))) m (syn_cnnc) dv_cache_0001 p0000
  have p0002 := @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A)
      (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))))
      (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x m
      dv_cache_0002
  have p0005 :=
    @g_elab2g
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m))))
        (syn_wne A (syn_c0)))
      x A (syn_cevenfin) (syn_cevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_cevenfin))
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m))))
        (syn_wne A (syn_c0)))
      p0005
  have p0007 := @g_addceq1 A (syn_cplc (.cv m) (.cv m)) (syn_c1c)
  have p0008 :=
    @g_reximi (.classEq A (syn_cplc (.cv m) (.cv m)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) m
      (syn_cnnc) p0007
  have p0009 :=
    @g_adantr (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m))))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
      (syn_wne A (syn_c0)) p0008
  have p0010 :=
    @g_syl (.classMem A (syn_cevenfin))
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq A (syn_cplc (.cv m) (.cv m))))
        (syn_wne A (syn_c0)))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
      p0006 p0009
  have p0011 :=
    @g_anim1i (.classMem A (syn_cevenfin))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
      (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0010
  have p0012 := @g_n_1cex
  have p0013 := @g_addcexg A (syn_c1c) (syn_cevenfin) (syn_cvv)
  have p0014 :=
    @g_mpan2 (.classMem A (syn_cevenfin)) (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_eqeq1 (.cv x) (syn_cplc A (syn_c1c))
      (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))
  have p0016 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc A (syn_c1c)))
      (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))) m
      (syn_cnnc) dv_cache_0005 p0015
  have p0017 := @g_neeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_c0)
  have p0018 :=
    @g_anbi12d (.classEq (.cv x) (syn_cplc A (syn_c1c)))
      (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0016 p0017
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x m
      dv_cache_0002
  have p0020 :=
    @g_elab2g
      (syn_wa (syn_wrex m (syn_cnnc)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c))
            (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
        (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
      x (syn_cplc A (syn_c1c)) (syn_coddfin) (syn_cvv) dv_cache_0006 dv_cache_0007 p0018
      p0019
  have p0021 :=
    @g_syl (.classMem A (syn_cevenfin)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin)) (syn_wa (syn_wrex m (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
          (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))))
      p0014 p0020
  have p0022 :=
    @g_adantr (.classMem A (syn_cevenfin))
      (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin)) (syn_wa (syn_wrex m (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
          (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))))
      (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0021
  have p0023 :=
    @g_mpbird
      (syn_wa (.classMem A (syn_cevenfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
      (.classMem (syn_cplc A (syn_c1c)) (syn_coddfin))
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c))
            (syn_cplc (syn_cplc (.cv m) (.cv m)) (syn_c1c))))
        (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
      p0011 p0022
  exact p0023

@[expose]
noncomputable def g_sucoddeven (A : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_coddfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
        (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin))) :=
  by
  let proofSupport : Finset Var := A.fv
  let m : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_m_ne_n : m ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_wa (syn_wrex n (syn_cnnc)
            (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
          (syn_wne A (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 :
    m ∉
      ((Wff.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    m ∉ ((Wff.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_A, fresh_m_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 :
    n ∉
      ((syn_wrex m (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_A, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((Wff.classEq (.cv x) (syn_cplc A (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_x, fresh_m_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 : m ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0012 : x ∉ ((syn_cplc A (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((syn_wa (syn_wrex m (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
          (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_m,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_eqeq1 (.cv x) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0001 :=
    @g_rexbidv (.classEq (.cv x) A)
      (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) n (syn_cnnc)
      dv_cache_0001 p0000
  have p0002 := @g_neeq1 (.cv x) A (syn_c0)
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A)
      (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne A (syn_c0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n
      dv_cache_0002
  have p0005 :=
    @g_elab2g
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      x A (syn_coddfin) (syn_coddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @g_ibi (.classMem A (syn_coddfin))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      p0005
  have p0007 := @g_peano2 (.cv n)
  have p0008 := @g_addc32 (.cv n) (.cv n) (syn_c1c)
  have p0009 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (.cv n)) (syn_c1c) p0008
  have p0010 := @g_addcass (syn_cplc (.cv n) (syn_c1c)) (.cv n) (syn_c1c)
  have p0011 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) p0009 p0010
  have p0012 :=
    @g_addceq12 (.cv m) (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0013 :=
    @g_anidms (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (.cv m))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
      p0012
  have p0014 :=
    @g_eqeq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv m) (.cv m))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)) p0013
  have p0015 :=
    @g_rspcev
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
        (syn_cplc (.cv m) (.cv m)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
      m (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0014
  have p0016 :=
    @g_mpan2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
          (syn_cplc (.cv m) (.cv m))))
      p0011 p0015
  have p0017 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
          (syn_cplc (.cv m) (.cv m))))
      p0007 p0016
  have p0018 := @g_addceq1 A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c)
  have p0019 :=
    @g_eqeq1d (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (syn_cplc A (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
      (syn_cplc (.cv m) (.cv m)) p0018
  have p0020 :=
    @g_rexbidv (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
        (syn_cplc (.cv m) (.cv m)))
      m (syn_cnnc) dv_cache_0008 p0019
  have p0021 :=
    @g_biimprd (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
          (syn_cplc (.cv m) (.cv m))))
      p0020
  have p0022 :=
    @g_com12 (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
          (syn_cplc (.cv m) (.cv m))))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      p0021
  have p0023 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wrex m (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c1c))
          (syn_cplc (.cv m) (.cv m))))
      (.imp (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (syn_wrex m (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m)))))
      p0017 p0022
  have p0024 :=
    @g_rexlimiv (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      n (syn_cnnc) dv_cache_0009 p0023
  have p0025 :=
    @g_adantr
      (syn_wrex n (syn_cnnc) (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      (syn_wne A (syn_c0)) p0024
  have p0026 :=
    @g_syl (.classMem A (syn_coddfin))
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) (syn_wne A (syn_c0)))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      p0006 p0025
  have p0027 :=
    @g_anim1i (.classMem A (syn_coddfin))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0026
  have p0028 := @g_n_1cex
  have p0029 := @g_addcexg A (syn_c1c) (syn_coddfin) (syn_cvv)
  have p0030 :=
    @g_mpan2 (.classMem A (syn_coddfin)) (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0028 p0029
  have p0031 := @g_eqeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))
  have p0032 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc A (syn_c1c)))
      (.classEq (.cv x) (syn_cplc (.cv m) (.cv m)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))) m (syn_cnnc)
      dv_cache_0010 p0031
  have p0033 := @g_neeq1 (.cv x) (syn_cplc A (syn_c1c)) (syn_c0)
  have p0034 :=
    @g_anbi12d (.classEq (.cv x) (syn_cplc A (syn_c1c)))
      (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))))
      (syn_wrex m (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
      (syn_wne (.cv x) (syn_c0)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0032 p0033
  have p0035 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x m
      dv_cache_0011
  have p0036 :=
    @g_elab2g
      (syn_wa (syn_wrex m (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv m) (.cv m))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wrex m (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
        (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
      x (syn_cplc A (syn_c1c)) (syn_cevenfin) (syn_cvv) dv_cache_0012 dv_cache_0013 p0034
      p0035
  have p0037 :=
    @g_syl (.classMem A (syn_coddfin)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
          (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))))
      p0030 p0036
  have p0038 :=
    @g_adantr (.classMem A (syn_coddfin))
      (syn_wb (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin)) (syn_wa (syn_wrex m (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
          (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))))
      (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)) p0037
  have p0039 :=
    @g_mpbird
      (syn_wa (.classMem A (syn_coddfin)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cevenfin))
      (syn_wa (syn_wrex m (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (.cv m) (.cv m))))
        (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
      p0027 p0038
  exact p0039

@[expose]
noncomputable def g_dfevenfin2 (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf
      (.classEq (syn_cevenfin) (.cab x (syn_wrex n (syn_cnnc)
            (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
              (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)))))) :=
  by
  have dv_cache_0001 : n ≠ x := by exact (show n ≠ x from (by exact dv_n_x))
  have dv_cache_0002 : n ∉ ((syn_wne (.cv x) (syn_c0))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_n_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n
      dv_cache_0001
  have p0001 :=
    @g_r19_41v (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0)) n
      (syn_cnnc) dv_cache_0002
  have p0002 := @g_neeq1 (.cv x) (syn_cplc (.cv n) (.cv n)) (syn_c0)
  have p0003 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0))
      (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)) p0002
  have p0004 :=
    @g_rexbii
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0)))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
        (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)))
      n (syn_cnnc) p0003
  have p0005 :=
    @g_bitr3i
      (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_wne (.cv x) (syn_c0))))
      (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
          (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))))
      p0001 p0004
  have p0006 :=
    @g_abbii
      (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
          (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0))))
      x p0005
  have p0007 :=
    @g_eqtri (syn_cevenfin)
      (.cab x (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
          (syn_wne (.cv x) (syn_c0))))
      (.cab x (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
            (syn_wne (syn_cplc (.cv n) (.cv n)) (syn_c0)))))
      p0000 p0006
  exact p0007

@[expose]
noncomputable def g_dfoddfin2 (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf
      (.classEq (syn_coddfin) (.cab x (syn_wrex n (syn_cnnc)
            (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
              (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))) :=
  by
  have dv_cache_0001 : n ≠ x := by exact (show n ≠ x from (by exact dv_n_x))
  have dv_cache_0002 : n ∉ ((syn_wne (.cv x) (syn_c0))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_n_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oddfin x n
      dv_cache_0001
  have p0001 :=
    @g_r19_41v (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (syn_wne (.cv x) (syn_c0)) n (syn_cnnc) dv_cache_0002
  have p0002 := @g_neeq1 (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)
  have p0003 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (syn_wne (.cv x) (syn_c0))
      (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0002
  have p0004 :=
    @g_rexbii
      (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
      n (syn_cnnc) p0003
  have p0005 :=
    @g_bitr3i
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
          (syn_wne (.cv x) (syn_c0))))
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
          (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))
      p0001 p0004
  have p0006 :=
    @g_abbii
      (syn_wa (syn_wrex n (syn_cnnc)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
          (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))
      x p0005
  have p0007 :=
    @g_eqtri (syn_coddfin)
      (.cab x (syn_wa (syn_wrex n (syn_cnnc)
            (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
          (syn_wne (.cv x) (syn_c0))))
      (.cab x (syn_wrex n (syn_cnnc)
          (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
            (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))))
      p0000 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_evenoddnnnul :
    Nominal.NPrf
      (.classEq (syn_cun (syn_cevenfin) (syn_coddfin))
        (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have dv_cache_0001 : x ∉ ((syn_cevenfin)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_coddfin)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 :
    m ∉ ((syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_n, not_false_eq_true])
  have dv_cache_0006 :
    m ∉
      ((Wff.imp (syn_wne (.cv k) (syn_c0))
          (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    k ∉
      ((Wff.imp (syn_wne (.cv m) (syn_c0))
          (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    m ∉
      ((Wff.imp (syn_wne (syn_c0c) (syn_c0))
          (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    m ∉
      ((Wff.imp (syn_wne (.cv n) (syn_c0))
          (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    m ∉
      ((Wff.imp (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
          (.classMem (syn_cplc (.cv k) (syn_c1c))
            (syn_cun (syn_cevenfin) (syn_coddfin))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : m ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0012 : n ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((syn_cun (syn_cevenfin) (syn_coddfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_evennn (.cv x)
  have p0001 := @g_evennnul (.cv x)
  have p0002 := @g_eldifsn (.cv x) (syn_cnnc) (syn_c0)
  have p0003 :=
    @g_sylanbrc (.classMem (.cv x) (syn_cevenfin)) (.classMem (.cv x) (syn_cnnc))
      (syn_wne (.cv x) (syn_c0))
      (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0000 p0001 p0002
  have p0004 :=
    @g_ssriv x (syn_cevenfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) dv_cache_0001
      dv_cache_0002 p0003
  have p0005 := @g_oddnn (.cv x)
  have p0006 := @g_oddnnul (.cv x)
  have p0007 :=
    @g_sylanbrc (.classMem (.cv x) (syn_coddfin)) (.classMem (.cv x) (syn_cnnc))
      (syn_wne (.cv x) (syn_c0))
      (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0005 p0006 p0002
  have p0008 :=
    @g_ssriv x (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) dv_cache_0003
      dv_cache_0002 p0007
  have p0009 :=
    @g_pm3_2i (syn_wss (syn_cevenfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (syn_wss (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0004 p0008
  have p0010 :=
    @g_unss (syn_cevenfin) (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))
  have p0011 :=
    @g_mpbi
      (syn_wa (syn_wss (syn_cevenfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
        (syn_wss (syn_coddfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))))
      (syn_wss (syn_cun (syn_cevenfin) (syn_coddfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      p0009 p0010
  have p0012 := @g_eldifsn (.cv n) (syn_cnnc) (syn_c0)
  have p0013 := @g_vex m
  have p0014 := @g_elsnc (.cv m) (syn_c0) p0013
  have p0015 := (Nominal.biimpRefl (syn_wne (.cv m) (syn_c0)))
  have p0016 := @g_con2bii (syn_wne (.cv m) (syn_c0)) (.classEq (.cv m) (syn_c0)) p0015
  have p0017 :=
    @g_bitri (.classMem (.cv m) (syn_csn (syn_c0))) (.classEq (.cv m) (syn_c0))
      (.neg (syn_wne (.cv m) (syn_c0))) p0014 p0016
  have p0018 :=
    @g_orbi1i (.classMem (.cv m) (syn_csn (syn_c0))) (.neg (syn_wne (.cv m) (syn_c0)))
      (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))) p0017
  have p0019 := @g_elun (.cv m) (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0020 :=
    @g_imor (syn_wne (.cv m) (syn_c0))
      (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
  have p0021 :=
    @g_n_3bitr4i
      (syn_wo (.classMem (.cv m) (syn_csn (syn_c0)))
        (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (syn_wo (.neg (syn_wne (.cv m) (syn_c0)))
        (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.classMem (.cv m) (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.imp (syn_wne (.cv m) (syn_c0))
        (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))
      p0018 p0019 p0020
  have p0022 :=
    @g_eqabi
      (.imp (syn_wne (.cv m) (syn_c0))
        (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))
      m (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin))) dv_cache_0004
      p0021
  have p0023 := @g_snex (syn_c0)
  have p0024 := @g_evenfinex
  have p0025 := @g_oddfinex
  have p0026 := @g_unex (syn_cevenfin) (syn_coddfin) p0024 p0025
  have p0027 :=
    @g_unex (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin)) p0023 p0026
  have p0028 :=
    @g_eqeltrri (syn_cun (syn_csn (syn_c0)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.cab m (.imp (syn_wne (.cv m) (syn_c0))
          (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))))
      (syn_cvv) p0022 p0027
  have p0029 := @g_neeq1 (.cv m) (syn_c0c) (syn_c0)
  have p0030 := @g_eleq1 (.cv m) (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0031 :=
    @g_imbi12d (.classEq (.cv m) (syn_c0c)) (syn_wne (.cv m) (syn_c0))
      (syn_wne (syn_c0c) (syn_c0))
      (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))) p0029 p0030
  have p0032 := @g_neeq1 (.cv m) (.cv k) (syn_c0)
  have p0033 := @g_eleq1 (.cv m) (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (syn_wb (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv k) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0034_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (syn_wb (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
          (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cevenfin syn_coddfin
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @g_imbi12d (.objEq m k) (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv k) (syn_c0))
      (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))) p0034_e00_recanon
      p0034_e01_recanon
  have p0035 := @g_neeq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (syn_c0)
  have p0036 :=
    @g_eleq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0037 :=
    @g_imbi12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wne (.cv m) (syn_c0))
      (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      p0035 p0036
  have p0038 := @g_neeq1 (.cv m) (.cv n) (syn_c0)
  have p0039 := @g_eleq1 (.cv m) (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))
  have p0040_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (syn_wb (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv n) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0040_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (syn_wb (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
          (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cevenfin syn_coddfin
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0040 :=
    @g_imbi12d (.objEq m n) (syn_wne (.cv m) (syn_c0)) (syn_wne (.cv n) (syn_c0))
      (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))) p0040_e00_recanon
      p0040_e01_recanon
  have p0041 := @g_ssun1 (syn_cevenfin) (syn_coddfin)
  have p0042 := @g_n_0ceven
  have p0043 :=
    @g_sselii (syn_cevenfin) (syn_cun (syn_cevenfin) (syn_coddfin)) (syn_c0c) p0041 p0042
  have p0044 :=
    @g_a1i (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (syn_wne (syn_c0c) (syn_c0)) p0043
  have p0045 := @g_addcnnul (.cv k) (syn_c1c)
  have p0046 :=
    @g_simpld (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (syn_wne (.cv k) (syn_c0))
      (syn_wne (syn_c1c) (syn_c0)) p0045
  have p0047 := @g_sucevenodd (.cv k)
  have p0048 :=
    @g_expcom (.classMem (.cv k) (syn_cevenfin))
      (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin)) p0047
  have p0049 := @g_sucoddeven (.cv k)
  have p0050 :=
    @g_expcom (.classMem (.cv k) (syn_coddfin))
      (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)) p0049
  have p0051 :=
    @g_orim12d (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (.classMem (.cv k) (syn_cevenfin))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin))
      (.classMem (.cv k) (syn_coddfin))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)) p0048 p0050
  have p0052 := @g_elun (.cv k) (syn_cevenfin) (syn_coddfin)
  have p0053 := @g_elun (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin) (syn_coddfin)
  have p0054 :=
    @g_orcom (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin))
  have p0055 :=
    @g_bitri
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (syn_wo (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin))
        (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin)))
      (syn_wo (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin))
        (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)))
      p0053 p0054
  have p0056 :=
    @g_n_3imtr4g (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (syn_wo (.classMem (.cv k) (syn_cevenfin)) (.classMem (.cv k) (syn_coddfin)))
      (syn_wo (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_coddfin))
        (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cevenfin)))
      (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      p0051 p0052 p0055
  have p0057 :=
    @g_embantd (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0)) (syn_wne (.cv k) (syn_c0))
      (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      p0046 p0056
  have p0058 :=
    @g_com12 (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
      (.imp (syn_wne (.cv k) (syn_c0))
        (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      p0057
  have p0059 :=
    @g_a1i
      (.imp (.imp (syn_wne (.cv k) (syn_c0))
          (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))
        (.imp (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
          (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin)))))
      (.classMem (.cv k) (syn_cnnc)) p0058
  have p0060_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (.cv n)) (syn_wb (.imp (syn_wne (.cv m) (syn_c0))
            (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))
          (.imp (syn_wne (.cv n) (syn_c0))
            (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv syn_cun syn_cevenfin syn_coddfin
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0040
  have p0060 :=
    @g_finds
      (.imp (syn_wne (.cv m) (syn_c0))
        (.classMem (.cv m) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.imp (syn_wne (syn_c0c) (syn_c0))
        (.classMem (syn_c0c) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.imp (syn_wne (.cv k) (syn_c0))
        (.classMem (.cv k) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.imp (syn_wne (syn_cplc (.cv k) (syn_c1c)) (syn_c0))
        (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cun (syn_cevenfin) (syn_coddfin))))
      (.imp (syn_wne (.cv n) (syn_c0))
        (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))))
      m k (.cv n) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0028 p0031 p0034 p0037 p0060_e04_recanon p0044 p0059
  have p0061 :=
    @g_imp (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0))
      (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))) p0060
  have p0062 :=
    @g_sylbi (.classMem (.cv n) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0)))
      (.classMem (.cv n) (syn_cun (syn_cevenfin) (syn_coddfin))) p0012 p0061
  have p0063 :=
    @g_ssriv n (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))
      (syn_cun (syn_cevenfin) (syn_coddfin)) dv_cache_0012 dv_cache_0013 p0062
  have p0064 :=
    @g_eqssi (syn_cun (syn_cevenfin) (syn_coddfin))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) p0011 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end
