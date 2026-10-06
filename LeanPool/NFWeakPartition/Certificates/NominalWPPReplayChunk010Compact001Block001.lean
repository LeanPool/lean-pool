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

/-- Checked nominal proof certificate identified upstream as `g_oddnn`. -/
@[expose]
noncomputable def gOddnn (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCoddfin)) (.classMem A (synCnnc))) :=
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
      ((synWa (synWrex n (synCnnc)
            (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
          (synWne A (synC0)))).fv :=
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
  have dv_cache_0005 : n ∉ ((Wff.classMem A (synCnnc))).fv :=
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
  have p0000 := @gEqeq1 (.cv x) A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) A)
      (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) n (synCnnc)
      dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) A (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne (.cv x) (synC0)) (synWne A (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x n
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      x A (synCoddfin) (synCoddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem A (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      p0005
  have p0007 := @gNncaddccl (.cv n) (.cv n)
  have p0008 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0007
  have p0009 := @gPeano2 (synCplc (.cv n) (.cv n))
  have p0010 := @gEleq1a (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synCnnc) A
  have p0011 :=
    @gN3syl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synCnnc))
      (.imp (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (.classMem A (synCnnc)))
      p0008 p0009 p0010
  have p0012 :=
    @gRexlimiv (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classMem A (synCnnc)) n (synCnnc) dv_cache_0005 p0011
  have p0013 :=
    @gAdantr
      (synWrex n (synCnnc) (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.classMem A (synCnnc)) (synWne A (synC0)) p0012
  have p0014 :=
    @gSyl (.classMem A (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      (.classMem A (synCnnc)) p0006 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_evennnul`. -/
@[expose]
noncomputable def gEvennnul (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCevenfin)) (synWne A (synC0))) :=
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
      ((synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
          (synWne A (synC0)))).fv :=
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
  have p0000 := @gEqeq1 (.cv x) A (synCplc (.cv n) (.cv n))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) A) (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
      (.classEq A (synCplc (.cv n) (.cv n))) n (synCnnc) dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) A (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
      (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
      (synWne (.cv x) (synC0)) (synWne A (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x n
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
        (synWne A (synC0)))
      x A (synCevenfin) (synCevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem A (synCevenfin))
      (synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
        (synWne A (synC0)))
      p0005
  have p0007 :=
    @gSimprd (.classMem A (synCevenfin))
      (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n)))) (synWne A (synC0))
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_oddnnul`. -/
@[expose]
noncomputable def gOddnnul (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCoddfin)) (synWne A (synC0))) :=
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
      ((synWa (synWrex n (synCnnc)
            (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
          (synWne A (synC0)))).fv :=
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
  have p0000 := @gEqeq1 (.cv x) A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) A)
      (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) n (synCnnc)
      dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) A (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne (.cv x) (synC0)) (synWne A (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x n
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      x A (synCoddfin) (synCoddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem A (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      p0005
  have p0007 :=
    @gSimprd (.classMem A (synCoddfin))
      (synWrex n (synCnnc) (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne A (synC0)) p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sucevenodd`. -/
@[expose]
noncomputable def gSucevenodd (A : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCevenfin)) (synWne (synCplc A (synC1c)) (synC0)))
        (.classMem (synCplc A (synC1c)) (synCoddfin))) :=
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
      ((synWa (synWrex m (synCnnc) (.classEq A (synCplc (.cv m) (.cv m))))
          (synWne A (synC0)))).fv :=
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
  have dv_cache_0005 : m ∉ ((Wff.classEq (.cv x) (synCplc A (synC1c)))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCplc A (synC1c))).fv :=
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
      ((synWa (synWrex m (synCnnc) (.classEq (synCplc A (synC1c))
              (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
          (synWne (synCplc A (synC1c)) (synC0)))).fv :=
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
  have p0000 := @gEqeq1 (.cv x) A (synCplc (.cv m) (.cv m))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) A) (.classEq (.cv x) (synCplc (.cv m) (.cv m)))
      (.classEq A (synCplc (.cv m) (.cv m))) m (synCnnc) dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) A (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A)
      (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (.cv m) (.cv m))))
      (synWrex m (synCnnc) (.classEq A (synCplc (.cv m) (.cv m))))
      (synWne (.cv x) (synC0)) (synWne A (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x m
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (.cv m) (.cv m))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex m (synCnnc) (.classEq A (synCplc (.cv m) (.cv m))))
        (synWne A (synC0)))
      x A (synCevenfin) (synCevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem A (synCevenfin))
      (synWa (synWrex m (synCnnc) (.classEq A (synCplc (.cv m) (.cv m))))
        (synWne A (synC0)))
      p0005
  have p0007 := @gAddceq1 A (synCplc (.cv m) (.cv m)) (synC1c)
  have p0008 :=
    @gReximi (.classEq A (synCplc (.cv m) (.cv m)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))) m
      (synCnnc) p0007
  have p0009 :=
    @gAdantr (synWrex m (synCnnc) (.classEq A (synCplc (.cv m) (.cv m))))
      (synWrex m (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWne A (synC0)) p0008
  have p0010 :=
    @gSyl (.classMem A (synCevenfin))
      (synWa (synWrex m (synCnnc) (.classEq A (synCplc (.cv m) (.cv m))))
        (synWne A (synC0)))
      (synWrex m (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      p0006 p0009
  have p0011 :=
    @gAnim1i (.classMem A (synCevenfin))
      (synWrex m (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWne (synCplc A (synC1c)) (synC0)) p0010
  have p0012 := @gN1cex
  have p0013 := @gAddcexg A (synC1c) (synCevenfin) (synCvv)
  have p0014 :=
    @gMpan2 (.classMem A (synCevenfin)) (.classMem (synC1c) (synCvv))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0012 p0013
  have p0015 :=
    @gEqeq1 (.cv x) (synCplc A (synC1c))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
  have p0016 :=
    @gRexbidv (.classEq (.cv x) (synCplc A (synC1c)))
      (.classEq (.cv x) (synCplc (synCplc (.cv m) (.cv m)) (synC1c)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))) m
      (synCnnc) dv_cache_0005 p0015
  have p0017 := @gNeeq1 (.cv x) (synCplc A (synC1c)) (synC0)
  have p0018 :=
    @gAnbi12d (.classEq (.cv x) (synCplc A (synC1c)))
      (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWrex m (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWne (.cv x) (synC0)) (synWne (synCplc A (synC1c)) (synC0)) p0016 p0017
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x m
      dv_cache_0002
  have p0020 :=
    @gElab2g
      (synWa (synWrex m (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex m (synCnnc) (.classEq (synCplc A (synC1c))
            (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
        (synWne (synCplc A (synC1c)) (synC0)))
      x (synCplc A (synC1c)) (synCoddfin) (synCvv) dv_cache_0006 dv_cache_0007 p0018
      p0019
  have p0021 :=
    @gSyl (.classMem A (synCevenfin)) (.classMem (synCplc A (synC1c)) (synCvv))
      (synWb (.classMem (synCplc A (synC1c)) (synCoddfin)) (synWa (synWrex m (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
          (synWne (synCplc A (synC1c)) (synC0))))
      p0014 p0020
  have p0022 :=
    @gAdantr (.classMem A (synCevenfin))
      (synWb (.classMem (synCplc A (synC1c)) (synCoddfin)) (synWa (synWrex m (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
          (synWne (synCplc A (synC1c)) (synC0))))
      (synWne (synCplc A (synC1c)) (synC0)) p0021
  have p0023 :=
    @gMpbird
      (synWa (.classMem A (synCevenfin)) (synWne (synCplc A (synC1c)) (synC0)))
      (.classMem (synCplc A (synC1c)) (synCoddfin))
      (synWa (synWrex m (synCnnc) (.classEq (synCplc A (synC1c))
            (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
        (synWne (synCplc A (synC1c)) (synC0)))
      p0011 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_sucoddeven`. -/
@[expose]
noncomputable def gSucoddeven (A : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCoddfin)) (synWne (synCplc A (synC1c)) (synC0)))
        (.classMem (synCplc A (synC1c)) (synCevenfin))) :=
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
      ((synWa (synWrex n (synCnnc)
            (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
          (synWne A (synC0)))).fv :=
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
  have dv_cache_0005 : m ∉ ((synCplc (.cv n) (synC1c))).fv :=
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
  have dv_cache_0006 : m ∉ ((synCnnc)).fv :=
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
      ((Wff.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
          (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))).fv :=
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
    m ∉ ((Wff.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))).fv :=
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
      ((synWrex m (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))).fv :=
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
  have dv_cache_0010 : m ∉ ((Wff.classEq (.cv x) (synCplc A (synC1c)))).fv :=
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
  have dv_cache_0012 : x ∉ ((synCplc A (synC1c))).fv :=
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
      ((synWa (synWrex m (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
          (synWne (synCplc A (synC1c)) (synC0)))).fv :=
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
  have p0000 := @gEqeq1 (.cv x) A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) A)
      (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) n (synCnnc)
      dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) A (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne (.cv x) (synC0)) (synWne A (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x n
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      x A (synCoddfin) (synCoddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem A (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      p0005
  have p0007 := @gPeano2 (.cv n)
  have p0008 := @gAddc32 (.cv n) (.cv n) (synC1c)
  have p0009 :=
    @gAddceq1i (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (synCplc (synCplc (.cv n) (synC1c)) (.cv n)) (synC1c) p0008
  have p0010 := @gAddcass (synCplc (.cv n) (synC1c)) (.cv n) (synC1c)
  have p0011 :=
    @gEqtri (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (.cv n)) (synC1c))
      (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))) p0009 p0010
  have p0012 :=
    @gAddceq12 (.cv m) (.cv m) (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))
  have p0013 :=
    @gAnidms (.classEq (.cv m) (synCplc (.cv n) (synC1c)))
      (.classEq (synCplc (.cv m) (.cv m))
        (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
      p0012
  have p0014 :=
    @gEqeq2d (.classEq (.cv m) (synCplc (.cv n) (synC1c))) (synCplc (.cv m) (.cv m))
      (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c)) p0013
  have p0015 :=
    @gRspcev
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
        (synCplc (.cv m) (.cv m)))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
      m (synCplc (.cv n) (synC1c)) (synCnnc) dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0014
  have p0016 :=
    @gMpan2 (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
      (synWrex m (synCnnc)
        (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
          (synCplc (.cv m) (.cv m))))
      p0011 p0015
  have p0017 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (synWrex m (synCnnc)
        (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
          (synCplc (.cv m) (.cv m))))
      p0007 p0016
  have p0018 := @gAddceq1 A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c)
  have p0019 :=
    @gEqeq1d (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synCplc A (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
      (synCplc (.cv m) (.cv m)) p0018
  have p0020 :=
    @gRexbidv (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m)))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
        (synCplc (.cv m) (.cv m)))
      m (synCnnc) dv_cache_0008 p0019
  have p0021 :=
    @gBiimprd (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      (synWrex m (synCnnc)
        (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
          (synCplc (.cv m) (.cv m))))
      p0020
  have p0022 :=
    @gCom12 (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWrex m (synCnnc)
        (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
          (synCplc (.cv m) (.cv m))))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      p0021
  have p0023 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWrex m (synCnnc)
        (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC1c))
          (synCplc (.cv m) (.cv m))))
      (.imp (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synWrex m (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m)))))
      p0017 p0022
  have p0024 :=
    @gRexlimiv (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      n (synCnnc) dv_cache_0009 p0023
  have p0025 :=
    @gAdantr
      (synWrex n (synCnnc) (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      (synWne A (synC0)) p0024
  have p0026 :=
    @gSyl (.classMem A (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne A (synC0)))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      p0006 p0025
  have p0027 :=
    @gAnim1i (.classMem A (synCoddfin))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      (synWne (synCplc A (synC1c)) (synC0)) p0026
  have p0028 := @gN1cex
  have p0029 := @gAddcexg A (synC1c) (synCoddfin) (synCvv)
  have p0030 :=
    @gMpan2 (.classMem A (synCoddfin)) (.classMem (synC1c) (synCvv))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0028 p0029
  have p0031 := @gEqeq1 (.cv x) (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))
  have p0032 :=
    @gRexbidv (.classEq (.cv x) (synCplc A (synC1c)))
      (.classEq (.cv x) (synCplc (.cv m) (.cv m)))
      (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))) m (synCnnc)
      dv_cache_0010 p0031
  have p0033 := @gNeeq1 (.cv x) (synCplc A (synC1c)) (synC0)
  have p0034 :=
    @gAnbi12d (.classEq (.cv x) (synCplc A (synC1c)))
      (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (.cv m) (.cv m))))
      (synWrex m (synCnnc) (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
      (synWne (.cv x) (synC0)) (synWne (synCplc A (synC1c)) (synC0)) p0032 p0033
  have p0035 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x m
      dv_cache_0011
  have p0036 :=
    @gElab2g
      (synWa (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (.cv m) (.cv m))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex m (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
        (synWne (synCplc A (synC1c)) (synC0)))
      x (synCplc A (synC1c)) (synCevenfin) (synCvv) dv_cache_0012 dv_cache_0013 p0034
      p0035
  have p0037 :=
    @gSyl (.classMem A (synCoddfin)) (.classMem (synCplc A (synC1c)) (synCvv))
      (synWb (.classMem (synCplc A (synC1c)) (synCevenfin)) (synWa (synWrex m (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
          (synWne (synCplc A (synC1c)) (synC0))))
      p0030 p0036
  have p0038 :=
    @gAdantr (.classMem A (synCoddfin))
      (synWb (.classMem (synCplc A (synC1c)) (synCevenfin)) (synWa (synWrex m (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
          (synWne (synCplc A (synC1c)) (synC0))))
      (synWne (synCplc A (synC1c)) (synC0)) p0037
  have p0039 :=
    @gMpbird
      (synWa (.classMem A (synCoddfin)) (synWne (synCplc A (synC1c)) (synC0)))
      (.classMem (synCplc A (synC1c)) (synCevenfin))
      (synWa (synWrex m (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (.cv m) (.cv m))))
        (synWne (synCplc A (synC1c)) (synC0)))
      p0027 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_dfevenfin2`. -/
@[expose]
noncomputable def gDfevenfin2 (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf
      (.classEq (synCevenfin) (.cab x (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
              (synWne (synCplc (.cv n) (.cv n)) (synC0)))))) :=
  by
  have dv_cache_0001 : n ≠ x := by exact (show n ≠ x from (by exact dv_n_x))
  have dv_cache_0002 : n ∉ ((synWne (.cv x) (synC0))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x n
      dv_cache_0001
  have p0001 :=
    @gR1941v (.classEq (.cv x) (synCplc (.cv n) (.cv n))) (synWne (.cv x) (synC0)) n
      (synCnnc) dv_cache_0002
  have p0002 := @gNeeq1 (.cv x) (synCplc (.cv n) (.cv n)) (synC0)
  have p0003 :=
    @gPm532i (.classEq (.cv x) (synCplc (.cv n) (.cv n))) (synWne (.cv x) (synC0))
      (synWne (synCplc (.cv n) (.cv n)) (synC0)) p0002
  have p0004 :=
    @gRexbii
      (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n))) (synWne (.cv x) (synC0)))
      (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
        (synWne (synCplc (.cv n) (.cv n)) (synC0)))
      n (synCnnc) p0003
  have p0005 :=
    @gBitr3i
      (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
        (synWne (.cv x) (synC0)))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n))) (synWne (.cv x) (synC0))))
      (synWrex n (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
          (synWne (synCplc (.cv n) (.cv n)) (synC0))))
      p0001 p0004
  have p0006 :=
    @gAbbii
      (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
        (synWne (.cv x) (synC0)))
      (synWrex n (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
          (synWne (synCplc (.cv n) (.cv n)) (synC0))))
      x p0005
  have p0007 :=
    @gEqtri (synCevenfin)
      (.cab x (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
          (synWne (.cv x) (synC0))))
      (.cab x (synWrex n (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
            (synWne (synCplc (.cv n) (.cv n)) (synC0)))))
      p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dfoddfin2`. -/
@[expose]
noncomputable def gDfoddfin2 (x : Var) (n : Var) (dv_n_x : n ≠ x) :
    Nominal.NPrf
      (.classEq (synCoddfin) (.cab x (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))) :=
  by
  have dv_cache_0001 : n ≠ x := by exact (show n ≠ x from (by exact dv_n_x))
  have dv_cache_0002 : n ∉ ((synWne (.cv x) (synC0))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x n
      dv_cache_0001
  have p0001 :=
    @gR1941v (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (.cv x) (synC0)) n (synCnnc) dv_cache_0002
  have p0002 := @gNeeq1 (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)
  have p0003 :=
    @gPm532i (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (.cv x) (synC0))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0002
  have p0004 :=
    @gRexbii
      (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWne (.cv x) (synC0)))
      (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      n (synCnnc) p0003
  have p0005 :=
    @gBitr3i
      (synWa (synWrex n (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (.cv x) (synC0))))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      p0001 p0004
  have p0006 :=
    @gAbbii
      (synWa (synWrex n (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      x p0005
  have p0007 :=
    @gEqtri (synCoddfin)
      (.cab x (synWa (synWrex n (synCnnc)
            (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
          (synWne (.cv x) (synC0))))
      (.cab x (synWrex n (synCnnc)
          (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
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

/-- Checked nominal proof certificate identified upstream as `g_evenoddnnnul`. -/
@[expose]
noncomputable def gEvenoddnnnul :
    Nominal.NPrf
      (.classEq (synCun (synCevenfin) (synCoddfin))
        (synCdif (synCnnc) (synCsn (synC0)))) :=
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
  have dv_cache_0001 : x ∉ ((synCevenfin)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCdif (synCnnc) (synCsn (synC0)))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCoddfin)).fv :=
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
    m ∉ ((synCun (synCsn (synC0)) (synCun (synCevenfin) (synCoddfin)))).fv :=
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
      ((Wff.imp (synWne (.cv k) (synC0))
          (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin))))).fv :=
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
      ((Wff.imp (synWne (.cv m) (synC0))
          (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))).fv :=
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
      ((Wff.imp (synWne (synC0c) (synC0))
          (.classMem (synC0c) (synCun (synCevenfin) (synCoddfin))))).fv :=
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
      ((Wff.imp (synWne (.cv n) (synC0))
          (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin))))).fv :=
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
      ((Wff.imp (synWne (synCplc (.cv k) (synC1c)) (synC0))
          (.classMem (synCplc (.cv k) (synC1c))
            (synCun (synCevenfin) (synCoddfin))))).fv :=
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
  have dv_cache_0012 : n ∉ ((synCdif (synCnnc) (synCsn (synC0)))).fv :=
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
  have dv_cache_0013 : n ∉ ((synCun (synCevenfin) (synCoddfin))).fv :=
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
  have p0000 := @gEvennn (.cv x)
  have p0001 := @gEvennnul (.cv x)
  have p0002 := @gEldifsn (.cv x) (synCnnc) (synC0)
  have p0003 :=
    @gSylanbrc (.classMem (.cv x) (synCevenfin)) (.classMem (.cv x) (synCnnc))
      (synWne (.cv x) (synC0))
      (.classMem (.cv x) (synCdif (synCnnc) (synCsn (synC0)))) p0000 p0001 p0002
  have p0004 :=
    @gSsriv x (synCevenfin) (synCdif (synCnnc) (synCsn (synC0))) dv_cache_0001
      dv_cache_0002 p0003
  have p0005 := @gOddnn (.cv x)
  have p0006 := @gOddnnul (.cv x)
  have p0007 :=
    @gSylanbrc (.classMem (.cv x) (synCoddfin)) (.classMem (.cv x) (synCnnc))
      (synWne (.cv x) (synC0))
      (.classMem (.cv x) (synCdif (synCnnc) (synCsn (synC0)))) p0005 p0006 p0002
  have p0008 :=
    @gSsriv x (synCoddfin) (synCdif (synCnnc) (synCsn (synC0))) dv_cache_0003
      dv_cache_0002 p0007
  have p0009 :=
    @gPm32i (synWss (synCevenfin) (synCdif (synCnnc) (synCsn (synC0))))
      (synWss (synCoddfin) (synCdif (synCnnc) (synCsn (synC0)))) p0004 p0008
  have p0010 :=
    @gUnss (synCevenfin) (synCoddfin) (synCdif (synCnnc) (synCsn (synC0)))
  have p0011 :=
    @gMpbi
      (synWa (synWss (synCevenfin) (synCdif (synCnnc) (synCsn (synC0))))
        (synWss (synCoddfin) (synCdif (synCnnc) (synCsn (synC0)))))
      (synWss (synCun (synCevenfin) (synCoddfin)) (synCdif (synCnnc) (synCsn (synC0))))
      p0009 p0010
  have p0012 := @gEldifsn (.cv n) (synCnnc) (synC0)
  have p0013 := @gVex m
  have p0014 := @gElsnc (.cv m) (synC0) p0013
  have p0015 := (Nominal.biimpRefl (synWne (.cv m) (synC0)))
  have p0016 := @gCon2bii (synWne (.cv m) (synC0)) (.classEq (.cv m) (synC0)) p0015
  have p0017 :=
    @gBitri (.classMem (.cv m) (synCsn (synC0))) (.classEq (.cv m) (synC0))
      (.neg (synWne (.cv m) (synC0))) p0014 p0016
  have p0018 :=
    @gOrbi1i (.classMem (.cv m) (synCsn (synC0))) (.neg (synWne (.cv m) (synC0)))
      (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))) p0017
  have p0019 := @gElun (.cv m) (synCsn (synC0)) (synCun (synCevenfin) (synCoddfin))
  have p0020 :=
    @gImor (synWne (.cv m) (synC0))
      (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
  have p0021 :=
    @gN3bitr4i
      (synWo (.classMem (.cv m) (synCsn (synC0)))
        (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))
      (synWo (.neg (synWne (.cv m) (synC0)))
        (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))
      (.classMem (.cv m) (synCun (synCsn (synC0)) (synCun (synCevenfin) (synCoddfin))))
      (.imp (synWne (.cv m) (synC0))
        (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))
      p0018 p0019 p0020
  have p0022 :=
    @gEqabi
      (.imp (synWne (.cv m) (synC0))
        (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))
      m (synCun (synCsn (synC0)) (synCun (synCevenfin) (synCoddfin))) dv_cache_0004
      p0021
  have p0023 := @gSnex (synC0)
  have p0024 := @gEvenfinex
  have p0025 := @gOddfinex
  have p0026 := @gUnex (synCevenfin) (synCoddfin) p0024 p0025
  have p0027 :=
    @gUnex (synCsn (synC0)) (synCun (synCevenfin) (synCoddfin)) p0023 p0026
  have p0028 :=
    @gEqeltrri (synCun (synCsn (synC0)) (synCun (synCevenfin) (synCoddfin)))
      (.cab m (.imp (synWne (.cv m) (synC0))
          (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))))
      (synCvv) p0022 p0027
  have p0029 := @gNeeq1 (.cv m) (synC0c) (synC0)
  have p0030 := @gEleq1 (.cv m) (synC0c) (synCun (synCevenfin) (synCoddfin))
  have p0031 :=
    @gImbi12d (.classEq (.cv m) (synC0c)) (synWne (.cv m) (synC0))
      (synWne (synC0c) (synC0))
      (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (synC0c) (synCun (synCevenfin) (synCoddfin))) p0029 p0030
  have p0032 := @gNeeq1 (.cv m) (.cv k) (synC0)
  have p0033 := @gEleq1 (.cv m) (.cv k) (synCun (synCevenfin) (synCoddfin))
  have p0034_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (synWb (synWne (.cv m) (synC0)) (synWne (.cv k) (synC0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0034_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (synWb (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
          (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCevenfin synCoddfin
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @gImbi12d (.objEq m k) (synWne (.cv m) (synC0)) (synWne (.cv k) (synC0))
      (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin))) p0034_e00_recanon
      p0034_e01_recanon
  have p0035 := @gNeeq1 (.cv m) (synCplc (.cv k) (synC1c)) (synC0)
  have p0036 :=
    @gEleq1 (.cv m) (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin))
  have p0037 :=
    @gImbi12d (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (synWne (.cv m) (synC0))
      (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin)))
      p0035 p0036
  have p0038 := @gNeeq1 (.cv m) (.cv n) (synC0)
  have p0039 := @gEleq1 (.cv m) (.cv n) (synCun (synCevenfin) (synCoddfin))
  have p0040_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (synWb (synWne (.cv m) (synC0)) (synWne (.cv n) (synC0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0040_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (synWb (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
          (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCevenfin synCoddfin
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0040 :=
    @gImbi12d (.objEq m n) (synWne (.cv m) (synC0)) (synWne (.cv n) (synC0))
      (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin))) p0040_e00_recanon
      p0040_e01_recanon
  have p0041 := @gSsun1 (synCevenfin) (synCoddfin)
  have p0042 := @gN0ceven
  have p0043 :=
    @gSselii (synCevenfin) (synCun (synCevenfin) (synCoddfin)) (synC0c) p0041 p0042
  have p0044 :=
    @gA1i (.classMem (synC0c) (synCun (synCevenfin) (synCoddfin)))
      (synWne (synC0c) (synC0)) p0043
  have p0045 := @gAddcnnul (.cv k) (synC1c)
  have p0046 :=
    @gSimpld (synWne (synCplc (.cv k) (synC1c)) (synC0)) (synWne (.cv k) (synC0))
      (synWne (synC1c) (synC0)) p0045
  have p0047 := @gSucevenodd (.cv k)
  have p0048 :=
    @gExpcom (.classMem (.cv k) (synCevenfin))
      (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (.classMem (synCplc (.cv k) (synC1c)) (synCoddfin)) p0047
  have p0049 := @gSucoddeven (.cv k)
  have p0050 :=
    @gExpcom (.classMem (.cv k) (synCoddfin))
      (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (.classMem (synCplc (.cv k) (synC1c)) (synCevenfin)) p0049
  have p0051 :=
    @gOrim12d (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (.classMem (.cv k) (synCevenfin))
      (.classMem (synCplc (.cv k) (synC1c)) (synCoddfin))
      (.classMem (.cv k) (synCoddfin))
      (.classMem (synCplc (.cv k) (synC1c)) (synCevenfin)) p0048 p0050
  have p0052 := @gElun (.cv k) (synCevenfin) (synCoddfin)
  have p0053 := @gElun (synCplc (.cv k) (synC1c)) (synCevenfin) (synCoddfin)
  have p0054 :=
    @gOrcom (.classMem (synCplc (.cv k) (synC1c)) (synCevenfin))
      (.classMem (synCplc (.cv k) (synC1c)) (synCoddfin))
  have p0055 :=
    @gBitri
      (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin)))
      (synWo (.classMem (synCplc (.cv k) (synC1c)) (synCevenfin))
        (.classMem (synCplc (.cv k) (synC1c)) (synCoddfin)))
      (synWo (.classMem (synCplc (.cv k) (synC1c)) (synCoddfin))
        (.classMem (synCplc (.cv k) (synC1c)) (synCevenfin)))
      p0053 p0054
  have p0056 :=
    @gN3imtr4g (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (synWo (.classMem (.cv k) (synCevenfin)) (.classMem (.cv k) (synCoddfin)))
      (synWo (.classMem (synCplc (.cv k) (synC1c)) (synCoddfin))
        (.classMem (synCplc (.cv k) (synC1c)) (synCevenfin)))
      (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin)))
      p0051 p0052 p0055
  have p0057 :=
    @gEmbantd (synWne (synCplc (.cv k) (synC1c)) (synC0)) (synWne (.cv k) (synC0))
      (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin)))
      p0046 p0056
  have p0058 :=
    @gCom12 (synWne (synCplc (.cv k) (synC1c)) (synC0))
      (.imp (synWne (.cv k) (synC0))
        (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin))))
      (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin)))
      p0057
  have p0059 :=
    @gA1i
      (.imp (.imp (synWne (.cv k) (synC0))
          (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin))))
        (.imp (synWne (synCplc (.cv k) (synC1c)) (synC0))
          (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin)))))
      (.classMem (.cv k) (synCnnc)) p0058
  have p0060_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (.cv n)) (synWb (.imp (synWne (.cv m) (synC0))
            (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))
          (.imp (synWne (.cv n) (synC0))
            (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv synCun synCevenfin synCoddfin
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0040
  have p0060 :=
    @gFinds
      (.imp (synWne (.cv m) (synC0))
        (.classMem (.cv m) (synCun (synCevenfin) (synCoddfin))))
      (.imp (synWne (synC0c) (synC0))
        (.classMem (synC0c) (synCun (synCevenfin) (synCoddfin))))
      (.imp (synWne (.cv k) (synC0))
        (.classMem (.cv k) (synCun (synCevenfin) (synCoddfin))))
      (.imp (synWne (synCplc (.cv k) (synC1c)) (synC0))
        (.classMem (synCplc (.cv k) (synC1c)) (synCun (synCevenfin) (synCoddfin))))
      (.imp (synWne (.cv n) (synC0))
        (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin))))
      m k (.cv n) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0028 p0031 p0034 p0037 p0060_e04_recanon p0044 p0059
  have p0061 :=
    @gImp (.classMem (.cv n) (synCnnc)) (synWne (.cv n) (synC0))
      (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin))) p0060
  have p0062 :=
    @gSylbi (.classMem (.cv n) (synCdif (synCnnc) (synCsn (synC0))))
      (synWa (.classMem (.cv n) (synCnnc)) (synWne (.cv n) (synC0)))
      (.classMem (.cv n) (synCun (synCevenfin) (synCoddfin))) p0012 p0061
  have p0063 :=
    @gSsriv n (synCdif (synCnnc) (synCsn (synC0)))
      (synCun (synCevenfin) (synCoddfin)) dv_cache_0012 dv_cache_0013 p0062
  have p0064 :=
    @gEqssi (synCun (synCevenfin) (synCoddfin))
      (synCdif (synCnnc) (synCsn (synC0))) p0011 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end
