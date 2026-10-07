/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisomemberrndownndv`. -/
@[expose]
noncomputable def gWecutisomemberrndownndv (w : Var) (v : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class)
    (hyp_wecutisomemberrndownndv_1 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
        (.classMem (.cv w) (synCrn (.cv f)))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪
        ({ f } : Finset Var) ∪
      E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_w : x ≠ w := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
          (.classMem (.cv w) (synCrn (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_ne_f, fresh_x_ne_w, fresh_x_not_E,
          fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0013 :
    u ∉
      ((Wff.imp (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
          (.classMem (.cv w) (synCrn (.cv f))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_v, fresh_u_ne_f, fresh_u_ne_w, fresh_u_not_E,
          fresh_u_not_S, or_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @gElwecutisodmrn x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011
  have p0001 :=
    @gA1i (synWbr S (synCwe) E)
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      hyp_wecutisomemberrndownndv_1
  have p0002 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
  have p0003 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0002
      p0003
  have p0005 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWbr S (synCwe) E) (.classMem (.cv u) E) p0001 p0004
  have p0006 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
  have p0007 :=
    @gSimpr
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
      p0006 p0007
  have p0009 :=
    @gSimpl (.classMem (.cv v) (synCrn (.cv f)))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
      (.classMem (.cv v) (synCrn (.cv f))) p0008 p0009
  have p0012 :=
    @gSimpl
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0006 p0012
  have p0014 :=
    @gSimpr
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0013 p0014
  have p0016 :=
    @gEleqtrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (.cv v) (synCrn (.cv f))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) p0010
      p0015
  have p0020 :=
    @gSimpr (.classMem (.cv v) (synCrn (.cv f)))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))) p0008 p0020
  have p0022 := @gSimpl (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))) (.classMem (.cv w) E)
      p0021 p0022
  have p0024 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classMem (.cv w) E) p0016 p0023
  have p0030 := @gSimpr (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
      (synWbr (.cv w) S (.cv v)) p0021 p0030
  have p0032 :=
    @gN3jca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synWa (synWbr S (synCwe) E) (.classMem (.cv u) E))
      (synWa (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (.classMem (.cv w) E))
      (synWbr (.cv w) S (.cv v)) p0005 p0024 p0031
  have p0033 := @gStrictsegdown u v w E S
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (synW3a (synWa (synWbr S (synCwe) E) (.classMem (.cv u) E)) (synWa (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (.classMem (.cv w) E)) (synWbr (.cv w) S (.cv v)))
      (.classMem (.cv w)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0032 p0033
  have p0040 :=
    @gEleqtrrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv v) (synCrn (.cv f)))
            (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))))
      (.cv w) (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCrn (.cv f)) p0034 p0015
  have p0041 :=
    @gExp32 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
      (.classMem (.cv w) (synCrn (.cv f))) p0040
  have p0042 :=
    @gRexlimivv
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.imp (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
        (.classMem (.cv w) (synCrn (.cv f))))
      x u D E dv_cache_0001 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWa (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f)) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      (.imp (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
        (.classMem (.cv w) (synCrn (.cv f))))
      p0000 p0042
  have p0044 :=
    @gImp (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
      (.classMem (.cv w) (synCrn (.cv f))) p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniondmdownndv`. -/
@[expose]
noncomputable def gWecutisouniondmdownndv (y : Var) (z : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisouniondmdownndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
        (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E))))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_y : f ≠ y := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_z : f ≠ z := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((synCwecutiso R D S E)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_y, not_false_eq_true])
  have dv_cache_0003 :
    f ∉
      ((Wff.imp (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
          (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_z, fresh_f_not_D, fresh_f_ne_y, fresh_f_not_R,
          fresh_f_not_E, fresh_f_not_S, or_false, not_false_eq_true])
  have p0000 := @gDmuni f (synCwecutiso R D S E) dv_cache_0001
  have p0001 :=
    @gEleq2i (synCdm (synCuni (synCwecutiso R D S E)))
      (synCiun f (synCwecutiso R D S E) (synCdm (.cv f))) (.cv y) p0000
  have p0002 := @gEliun f (.cv y) (synCwecutiso R D S E) (synCdm (.cv f)) dv_cache_0002
  have p0003 :=
    @gBitri (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv y) (synCiun f (synCwecutiso R D S E) (synCdm (.cv f))))
      (synWrex f (synCwecutiso R D S E) (.classMem (.cv y) (synCdm (.cv f)))) p0001
      p0002
  have p0004 :=
    @gBiimpi (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (synWrex f (synCwecutiso R D S E) (.classMem (.cv y) (synCdm (.cv f)))) p0003
  have p0005 := @gWecutisomemberdmdownndv y z D R S f E hyp_wecutisouniondmdownndv_1
  have p0006 :=
    @gSimpl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
  have p0007 := @gElssuni (.cv f) (synCwecutiso R D S E)
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
      (.classMem (.cv f) (synCwecutiso R D S E))
      (synWss (.cv f) (synCuni (synCwecutiso R D S E))) p0006 p0007
  have p0009 := @gDmss (.cv f) (synCuni (synCwecutiso R D S E))
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
      (synWss (.cv f) (synCuni (synCwecutiso R D S E)))
      (synWss (synCdm (.cv f)) (synCdm (synCuni (synCwecutiso R D S E)))) p0008 p0009
  have p0011 :=
    @gSsel (synCdm (.cv f)) (synCdm (synCuni (synCwecutiso R D S E))) (.cv z)
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
      (synWss (synCdm (.cv f)) (synCdm (synCuni (synCwecutiso R D S E))))
      (.imp (.classMem (.cv z) (synCdm (.cv f)))
        (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))))
      p0010 p0011
  have p0013 :=
    @gMpd
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
      (.classMem (.cv z) (synCdm (.cv f)))
      (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))) p0005 p0012
  have p0014 :=
    @gExp32 (.classMem (.cv f) (synCwecutiso R D S E))
      (.classMem (.cv y) (synCdm (.cv f)))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))) p0013
  have p0015 :=
    @gRexlimiv (.classMem (.cv y) (synCdm (.cv f)))
      (.imp (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
        (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))))
      f (synCwecutiso R D S E) dv_cache_0003 p0014
  have p0016 :=
    @gSyl (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (synWrex f (synCwecutiso R D S E) (.classMem (.cv y) (synCdm (.cv f))))
      (.imp (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
        (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))))
      p0004 p0015
  have p0017 :=
    @gImp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv z) (synCdm (synCuni (synCwecutiso R D S E)))) p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionrndownndv`. -/
@[expose]
noncomputable def gWecutisounionrndownndv (w : Var) (v : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisounionrndownndv_1 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
        (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E))))) :=
  by
  let proofSupport : Finset Var :=
    ({ w } : Finset Var) ∪ ({ v } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_w : f ≠ w := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_v : f ≠ v := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((synCwecutiso R D S E)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_v, not_false_eq_true])
  have dv_cache_0003 :
    f ∉
      ((Wff.imp (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
          (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_w, fresh_f_not_E, fresh_f_ne_v, fresh_f_not_S,
          fresh_f_not_D, fresh_f_not_R, or_false, not_false_eq_true])
  have p0000 := @gRnuni f (synCwecutiso R D S E) dv_cache_0001
  have p0001 :=
    @gEleq2i (synCrn (synCuni (synCwecutiso R D S E)))
      (synCiun f (synCwecutiso R D S E) (synCrn (.cv f))) (.cv v) p0000
  have p0002 := @gEliun f (.cv v) (synCwecutiso R D S E) (synCrn (.cv f)) dv_cache_0002
  have p0003 :=
    @gBitri (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv v) (synCiun f (synCwecutiso R D S E) (synCrn (.cv f))))
      (synWrex f (synCwecutiso R D S E) (.classMem (.cv v) (synCrn (.cv f)))) p0001
      p0002
  have p0004 :=
    @gBiimpi (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (synWrex f (synCwecutiso R D S E) (.classMem (.cv v) (synCrn (.cv f)))) p0003
  have p0005 := @gWecutisomemberrndownndv w v D R S f E hyp_wecutisounionrndownndv_1
  have p0006 :=
    @gSimpl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (.classMem (.cv v) (synCrn (.cv f)))
        (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v))))
  have p0007 := @gElssuni (.cv f) (synCwecutiso R D S E)
  have p0008 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
      (.classMem (.cv f) (synCwecutiso R D S E))
      (synWss (.cv f) (synCuni (synCwecutiso R D S E))) p0006 p0007
  have p0009 := @gRnss (.cv f) (synCuni (synCwecutiso R D S E))
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
      (synWss (.cv f) (synCuni (synCwecutiso R D S E)))
      (synWss (synCrn (.cv f)) (synCrn (synCuni (synCwecutiso R D S E)))) p0008 p0009
  have p0011 :=
    @gSsel (synCrn (.cv f)) (synCrn (synCuni (synCwecutiso R D S E))) (.cv w)
  have p0012 :=
    @gSyl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
      (synWss (synCrn (.cv f)) (synCrn (synCuni (synCwecutiso R D S E))))
      (.imp (.classMem (.cv w) (synCrn (.cv f)))
        (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))))
      p0010 p0011
  have p0013 :=
    @gMpd
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem (.cv v) (synCrn (.cv f)))
          (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))))
      (.classMem (.cv w) (synCrn (.cv f)))
      (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))) p0005 p0012
  have p0014 :=
    @gExp32 (.classMem (.cv f) (synCwecutiso R D S E))
      (.classMem (.cv v) (synCrn (.cv f)))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
      (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))) p0013
  have p0015 :=
    @gRexlimiv (.classMem (.cv v) (synCrn (.cv f)))
      (.imp (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
        (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))))
      f (synCwecutiso R D S E) dv_cache_0003 p0014
  have p0016 :=
    @gSyl (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (synWrex f (synCwecutiso R D S E) (.classMem (.cv v) (synCrn (.cv f))))
      (.imp (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
        (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))))
      p0004 p0015
  have p0017 :=
    @gImp (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (.classMem (.cv w) E) (synWbr (.cv w) S (.cv v)))
      (.classMem (.cv w) (synCrn (synCuni (synCwecutiso R D S E)))) p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniondmsscutndv`. -/
@[expose]
noncomputable def gWecutisouniondmsscutndv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (hyp_wecutisouniondmsscutndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((synCdm (synCuni (synCwecutiso R D S E)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R,
          fresh_y_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
  have p0001 := @gWecutisouniondmrnss D R S E
  have p0002 :=
    @gSimpli (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWss (synCrn (synCuni (synCwecutiso R D S E))) E) p0001
  have p0003 := @gSseli (synCdm (synCuni (synCwecutiso R D S E))) D (.cv y) p0002
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv y) D) p0000 p0003
  have p0005 := @gId (synWbr (.cv y) R (.cv x))
  have p0006 :=
    @gA1i (.imp (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      p0005
  have p0007 :=
    @gSimpl
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
  have p0008 :=
    @gSimpr (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))) p0007 p0008
  have p0010 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv x) R (.cv y))
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))) p0010 p0000
  have p0015 :=
    @gSimpl (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv x) D) p0007 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv x) D) p0010 p0016
  have p0018 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv x) R (.cv y))
  have p0019 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) (synWbr (.cv x) R (.cv y)) p0017 p0018
  have p0020 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (synWa (.classMem (.cv x) D) (synWbr (.cv x) R (.cv y))) p0012 p0019
  have p0021 := @gWecutisouniondmdownndv y x D R S E hyp_wecutisouniondmsscutndv_1
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
        (synWa (.classMem (.cv x) D) (synWbr (.cv x) R (.cv y))))
      (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))) p0020 p0021
  have p0023 :=
    @gEx
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv x) R (.cv y))
      (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))) p0022
  have p0024 :=
    @gMtod
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv x) R (.cv y))
      (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))) p0009 p0023
  have p0025 :=
    @gPm221d
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)) p0024
  have p0026 := @gWppweconnex D R
  have p0027 := Nominal.mp hyp_wecutisouniondmsscutndv_1 p0026
  have p0028 :=
    @gA1i (synWbr R (synCconnex) D)
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      p0027
  have p0037 :=
    @gConnexd
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      D R (.cv y) (.cv x) p0028 p0004 p0016
  have p0038 :=
    @gMpjaod
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) R (.cv x)) (synWbr (.cv x) R (.cv y))
      p0006 p0025 p0037
  have p0043 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))) p0000 p0009
  have p0044 := @gNelne2 (.cv y) (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))
  have p0045 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWne (.cv y) (.cv x)) p0043 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)) p0038 p0045
  have p0047 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv y) D) (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
      p0004 p0046
  have p0048 := @gElstrictseg x y D R
  have p0049 :=
    @gSylibr
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0047 p0048
  have p0050 :=
    @gEx
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0049
  have p0051 :=
    @gSsrdv
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      y (synCdm (synCuni (synCwecutiso R D S E)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0050
  exact p0051

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionrnsscutndv`. -/
@[expose]
noncomputable def gWecutisounionrnsscutndv (u : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (hyp_wecutisounionrnsscutndv_1 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ ((synCrn (synCuni (synCwecutiso R D S E)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_v_not_D, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    v ∉ ((synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    v ∉
      ((synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_D, fresh_v_not_R,
          fresh_v_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
  have p0001 := @gWecutisouniondmrnss D R S E
  have p0002 :=
    @gSimpri (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWss (synCrn (synCuni (synCwecutiso R D S E))) E) p0001
  have p0003 := @gSseli (synCrn (synCuni (synCwecutiso R D S E))) E (.cv v) p0002
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv v) E) p0000 p0003
  have p0005 := @gId (synWbr (.cv v) S (.cv u))
  have p0006 :=
    @gA1i (.imp (synWbr (.cv v) S (.cv u)) (synWbr (.cv v) S (.cv u)))
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      p0005
  have p0007 :=
    @gSimpl
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
  have p0008 :=
    @gSimpr (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))) p0007 p0008
  have p0010 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv u) S (.cv v))
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv u) S (.cv v)))
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))) p0010 p0000
  have p0015 :=
    @gSimpl (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv u) E) p0007 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv u) S (.cv v)))
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv u) E) p0010 p0016
  have p0018 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv u) S (.cv v))
  have p0019 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv u) S (.cv v)))
      (.classMem (.cv u) E) (synWbr (.cv u) S (.cv v)) p0017 p0018
  have p0020 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv u) S (.cv v)))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (.classMem (.cv u) E) (synWbr (.cv u) S (.cv v))) p0012 p0019
  have p0021 := @gWecutisounionrndownndv u v D R S E hyp_wecutisounionrnsscutndv_1
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
        (synWbr (.cv u) S (.cv v)))
      (synWa (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
        (synWa (.classMem (.cv u) E) (synWbr (.cv u) S (.cv v))))
      (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))) p0020 p0021
  have p0023 :=
    @gEx
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv u) S (.cv v))
      (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))) p0022
  have p0024 :=
    @gMtod
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv u) S (.cv v))
      (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))) p0009 p0023
  have p0025 :=
    @gPm221d
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv u) S (.cv v)) (synWbr (.cv v) S (.cv u)) p0024
  have p0026 := @gWppweconnex E S
  have p0027 := Nominal.mp hyp_wecutisounionrnsscutndv_1 p0026
  have p0028 :=
    @gA1i (synWbr S (synCconnex) E)
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      p0027
  have p0037 :=
    @gConnexd
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      E S (.cv v) (.cv u) p0028 p0004 p0016
  have p0038 :=
    @gMpjaod
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv v) S (.cv u)) (synWbr (.cv v) S (.cv u)) (synWbr (.cv u) S (.cv v))
      p0006 p0025 p0037
  have p0043 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))) p0000 p0009
  have p0044 := @gNelne2 (.cv v) (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))
  have p0045 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWne (.cv v) (.cv u)) p0043 p0044
  have p0046 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u)) p0038 p0045
  have p0047 :=
    @gJca
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (.classMem (.cv v) E) (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u)))
      p0004 p0046
  have p0048 := @gElstrictseg u v E S
  have p0049 :=
    @gSylibr
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (.cv v) E)
        (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0047 p0048
  have p0050 :=
    @gEx
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0049
  have p0051 :=
    @gSsrdv
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      v (synCrn (synCuni (synCwecutiso R D S E)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0050
  exact p0051

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniondmexactcutndv`. -/
@[expose]
noncomputable def gWecutisouniondmexactcutndv (x : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisouniondmexactcutndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x)))))
        (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    y ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCdm (synCuni (synCwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R,
          fresh_y_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
        (synCima R (synCsn (.cv x))))
  have p0001 := @gWecutisouniondmsscutndv x D R S E hyp_wecutisouniondmexactcutndv_1
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWss (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0000 p0001
  have p0003 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0004 := @gElstrictseg x y D R
  have p0005 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0003 p0004
  have p0006 :=
    @gSimprr (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (synWne (.cv y) (.cv x)) p0005 p0006
  have p0008 := @gWppweantisym D R
  have p0009 := Nominal.mp hyp_wecutisouniondmexactcutndv_1 p0008
  have p0010 :=
    @gA1i (synWbr R (synCantisym) D)
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0015 :=
    @gSimpl (.classMem (.cv y) D)
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y) D) p0005 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y) D) p0011 p0016
  have p0019 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      p0011 p0019
  have p0022 :=
    @gSimpl (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv x) D) p0000 p0022
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (.classMem (.cv x) D) p0020 p0023
  have p0029 :=
    @gSimprl (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (synWbr (.cv y) R (.cv x)) p0005 p0029
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x)) p0011 p0030
  have p0035 :=
    @gSimpr
      (synWa (.classMem (.cv x) D)
        (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
        (synCima R (synCsn (.cv x))))
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
        (synCima R (synCsn (.cv x))))
      p0020 p0035
  have p0044 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0045 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv y) D)
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0017 p0044
  have p0046 := @gEldif (.cv y) D (synCdm (synCuni (synCwecutiso R D S E)))
  have p0047 :=
    @gSylibr
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWa (.classMem (.cv y) D)
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv y) (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))) p0045
      p0046
  have p0048 :=
    @gSseldd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
      (synCima R (synCsn (.cv x))) (.cv y) p0036 p0047
  have p0049 := @gElimasn R (.cv x) (.cv y)
  have p0050 := (Nominal.biimpRefl (synWbr (.cv x) R (.cv y)))
  have p0051 :=
    @gBitr4i (.classMem (.cv y) (synCima R (synCsn (.cv x))))
      (.classMem (synCop (.cv x) (.cv y)) R) (synWbr (.cv x) R (.cv y)) p0049 p0050
  have p0052 :=
    @gSylib
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv y) (synCima R (synCsn (.cv x)))) (synWbr (.cv x) R (.cv y)) p0048
      p0051
  have p0053 :=
    @gAntid
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D)
              (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
              (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      D R (.cv y) (.cv x) p0010 p0017 p0024 p0031 p0052
  have p0054 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classEq (.cv y) (.cv x)) p0053
  have p0055 :=
    @gNecon3ad
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.cv y)
      (.cv x) p0054
  have p0056 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWne (.cv y) (.cv x))
      (.neg (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))) p0007
      p0055
  have p0057 :=
    @gNotnotrd
      (synWa (synWa (synWa (.classMem (.cv x) D)
            (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
            (synCima R (synCsn (.cv x))))) (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))) p0056
  have p0058 :=
    @gEx
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))) p0057
  have p0059 :=
    @gSsrdv
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      y (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCdm (synCuni (synCwecutiso R D S E))) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0058
  have p0060 :=
    @gEqssd
      (synWa (synWa (.classMem (.cv x) D)
          (.neg (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif D (synCdm (synCuni (synCwecutiso R D S E))))
          (synCima R (synCsn (.cv x)))))
      (synCdm (synCuni (synCwecutiso R D S E)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0002
      p0059
  exact p0060


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionrnexactcutndv`. -/
@[expose]
noncomputable def gWecutisounionrnexactcutndv (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class)
    (hyp_wecutisounionrnexactcutndv_1 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u)))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    v ∉ ((synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_not_E, fresh_v_not_S, fresh_v_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((synCrn (synCuni (synCwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_v_not_D, fresh_v_not_E, fresh_v_not_R, fresh_v_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    v ∉
      ((synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_E, fresh_v_not_D, fresh_v_not_R,
          fresh_v_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
        (synCima S (synCsn (.cv u))))
  have p0001 := @gWecutisounionrnsscutndv u D R S E hyp_wecutisounionrnexactcutndv_1
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWss (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0000 p0001
  have p0003 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0004 := @gElstrictseg u v E S
  have p0005 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classMem (.cv v) E)
        (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))))
      p0003 p0004
  have p0006 :=
    @gSimprr (.classMem (.cv v) E) (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv v) E)
        (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))))
      (synWne (.cv v) (.cv u)) p0005 p0006
  have p0008 := @gWppweantisym E S
  have p0009 := Nominal.mp hyp_wecutisounionrnexactcutndv_1 p0008
  have p0010 :=
    @gA1i (synWbr S (synCantisym) E)
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
  have p0015 :=
    @gSimpl (.classMem (.cv v) E)
      (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u)))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv v) E)
        (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))))
      (.classMem (.cv v) E) p0005 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classMem (.cv v) E) p0011 p0016
  have p0019 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      p0011 p0019
  have p0022 :=
    @gSimpl (.classMem (.cv u) E)
      (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E)))))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv u) E) p0000 p0022
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (.classMem (.cv u) E) p0020 p0023
  have p0029 :=
    @gSimprl (.classMem (.cv v) E) (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv v) E)
        (synWa (synWbr (.cv v) S (.cv u)) (synWne (.cv v) (.cv u))))
      (synWbr (.cv v) S (.cv u)) p0005 p0029
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWbr (.cv v) S (.cv u)) p0011 p0030
  have p0035 :=
    @gSimpr
      (synWa (.classMem (.cv u) E)
        (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
        (synCima S (synCsn (.cv u))))
  have p0036 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
        (synCima S (synCsn (.cv u))))
      p0020 p0035
  have p0044 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
  have p0045 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv v) E)
      (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))) p0017 p0044
  have p0046 := @gEldif (.cv v) E (synCrn (synCuni (synCwecutiso R D S E)))
  have p0047 :=
    @gSylibr
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synWa (.classMem (.cv v) E)
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv v) (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))) p0045
      p0046
  have p0048 :=
    @gSseldd
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
      (synCima S (synCsn (.cv u))) (.cv v) p0036 p0047
  have p0049 := @gElimasn S (.cv u) (.cv v)
  have p0050 := (Nominal.biimpRefl (synWbr (.cv u) S (.cv v)))
  have p0051 :=
    @gBitr4i (.classMem (.cv v) (synCima S (synCsn (.cv u))))
      (.classMem (synCop (.cv u) (.cv v)) S) (synWbr (.cv u) S (.cv v)) p0049 p0050
  have p0052 :=
    @gSylib
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      (.classMem (.cv v) (synCima S (synCsn (.cv u)))) (synWbr (.cv u) S (.cv v)) p0048
      p0051
  have p0053 :=
    @gAntid
      (synWa (synWa (synWa (synWa (.classMem (.cv u) E)
              (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
            (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
              (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))))
      E S (.cv v) (.cv u) p0010 p0017 p0024 p0031 p0052
  have p0054 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))
      (.classEq (.cv v) (.cv u)) p0053
  have p0055 :=
    @gNecon3ad
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E))))) (.cv v)
      (.cv u) p0054
  have p0056 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWne (.cv v) (.cv u))
      (.neg (.neg (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))))) p0007
      p0055
  have p0057 :=
    @gNotnotrd
      (synWa (synWa (synWa (.classMem (.cv u) E)
            (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
          (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
            (synCima S (synCsn (.cv u))))) (.classMem (.cv v)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))) p0056
  have p0058 :=
    @gEx
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (.classMem (.cv v)
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classMem (.cv v) (synCrn (synCuni (synCwecutiso R D S E)))) p0057
  have p0059 :=
    @gSsrdv
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      v (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCrn (synCuni (synCwecutiso R D S E))) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0058
  have p0060 :=
    @gEqssd
      (synWa (synWa (.classMem (.cv u) E)
          (.neg (.classMem (.cv u) (synCrn (synCuni (synCwecutiso R D S E))))))
        (synWss (synCdif E (synCrn (synCuni (synCwecutiso R D S E))))
          (synCima S (synCsn (.cv u)))))
      (synCrn (synCuni (synCwecutiso R D S E)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) p0002
      p0059
  exact p0060

/-- Checked nominal proof certificate identified upstream as `g_wecutisoaddpairf1ondv`. -/
@[expose]
noncomputable def gWecutisoaddpairf1ondv (x : Var) (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWf1o (synCun H (synCsn (synCop (.cv x) (.cv u)))) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))))) :=
  by
  have p0000 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWiso H R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0001 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S H
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso H R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0000 p0001
  have p0003 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWiso H R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0004 := @gF1osng (.cv x) (.cv u) D E
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWf1o (synCsn (synCop (.cv x) (.cv u))) (synCsn (.cv x)) (synCsn (.cv u)))
      p0003 p0004
  have p0006 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWf1o H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o (synCsn (synCop (.cv x) (.cv u))) (synCsn (.cv x)) (synCsn (.cv u)))
      p0002 p0005
  have p0007 := @gStrictsegnel x D R
  have p0008 :=
    @gDisjsn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (.cv x)
  have p0009 :=
    @gMpbir
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synC0))
      (.neg (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0007 p0008
  have p0010 :=
    @gA1i
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synC0))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0009
  have p0011 := @gStrictsegnel u E S
  have p0012 :=
    @gDisjsn (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (.cv u)
  have p0013 :=
    @gMpbir
      (.classEq (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) (synC0))
      (.neg (.classMem (.cv u)
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0011 p0012
  have p0014 :=
    @gA1i
      (.classEq (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) (synC0))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0013
  have p0015 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synC0))
      (.classEq (synCin
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) (synC0))
      p0010 p0014
  have p0016 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWf1o H
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWf1o (synCsn (synCop (.cv x) (.cv u))) (synCsn (.cv x)) (synCsn (.cv u))))
      (synWa (.classEq (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) (synC0)) (.classEq (synCin
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) (synC0)))
      p0006 p0015
  have p0017 :=
    @gF1oun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCsn (.cv x)) (synCsn (.cv u)) H (synCsn (synCop (.cv x) (.cv u)))
  have p0018 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso H R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (synWf1o H
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWf1o (synCsn (synCop (.cv x) (.cv u))) (synCsn (.cv x)) (synCsn (.cv u))))
        (synWa (.classEq (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))) (synC0)) (.classEq (synCin
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) (synC0))))
      (synWf1o (synCun H (synCsn (synCop (.cv x) (.cv u)))) (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0016 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisoaddpairisondv`. -/
@[expose]
noncomputable def gWecutisoaddpairisondv (x : Var) (u : Var) (D : Class) (R : Class)
    (S : Class) (E : Class) (H : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
            (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))) (synWiso H R S
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWiso (synCun H (synCsn (synCop (.cv x) (.cv u)))) R S (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ H.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synWa (synWa (synWa (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
              (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))) (synWiso H R S
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_not_S,
          fresh_z_not_E, fresh_z_ne_x, fresh_z_ne_u, fresh_z_not_H, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 :
    y ∉
      ((synWa (synWa (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
            (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))) (synWiso H R S
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, fresh_y_not_S,
          fresh_y_not_E, fresh_y_ne_x, fresh_y_ne_u, fresh_y_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    y ∉
      ((synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_E, fresh_y_not_S, fresh_y_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_E, fresh_z_not_S, fresh_z_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synCun H (synCsn (synCop (.cv x) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_H, fresh_y_ne_x, fresh_y_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ ((synCun H (synCsn (synCop (.cv x) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_H, fresh_z_ne_x, fresh_z_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0011 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0012 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0013 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0014 : z ∉ (S).fv :=
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
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  let syntaxFormula0000 : Wff :=
    (synWa (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)))
  let syntaxFormula0001 : Wff :=
    (synWiso H R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxFormula0002 : Wff := (synWa syntaxFormula0000 syntaxFormula0001)
  let syntaxFormula0003 : Wff :=
    (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) syntaxFormula0001)
  let syntaxClass0004 : Class :=
    (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCsn (.cv x)))
  let syntaxClass0005 : Class :=
    (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCsn (.cv u)))
  let syntaxFormula0006 : Wff :=
    (synWf1o (synCun H (synCsn (synCop (.cv x) (.cv u)))) syntaxClass0004 syntaxClass0005)
  let syntaxFormula0007 : Wff := (.classMem (.cv y) syntaxClass0004)
  let syntaxFormula0008 : Wff := (synWa syntaxFormula0002 syntaxFormula0007)
  let syntaxFormula0009 : Wff := (.classMem (.cv z) syntaxClass0004)
  let syntaxFormula0010 : Wff := (synWa syntaxFormula0008 syntaxFormula0009)
  let syntaxFormula0011 : Wff :=
    (.classMem (.cv y)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0012 : Wff := (synWa syntaxFormula0010 syntaxFormula0011)
  let syntaxFormula0013 : Wff :=
    (.classMem (.cv z)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  let syntaxFormula0014 : Wff := (synWa syntaxFormula0012 syntaxFormula0013)
  let syntaxFormula0015 : Wff := (synWa syntaxFormula0011 syntaxFormula0013)
  let syntaxClass0016 : Class :=
    (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))
  let syntaxFormula0017 : Wff :=
    (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      syntaxClass0016)
  let syntaxFormula0018 : Wff := (.classMem (.cv y) syntaxClass0016)
  let syntaxFormula0019 : Wff :=
    (synWa (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.neg (.classMem (.cv y) (synCsn (.cv x)))))
  let syntaxFormula0020 : Wff := (.classMem (.cv z) syntaxClass0016)
  let syntaxFormula0021 : Wff :=
    (synWa (.classMem (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.neg (.classMem (.cv z) (synCsn (.cv x)))))
  let syntaxFormula0022 : Wff :=
    (synWbr (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y)) S
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z)))
  let syntaxFormula0023 : Wff := (synWb (synWbr (.cv y) R (.cv z)) syntaxFormula0022)
  let syntaxFormula0024 : Wff := (synWa syntaxFormula0012 (.classEq (.cv z) (.cv x)))
  let syntaxFormula0025 : Wff :=
    (synWf1o H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxFormula0026 : Wff :=
    (synWf H (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxClass0027 : Class :=
    (synCdif (synCin E (synCima (synCcnv S) (synCsn (.cv u)))) (synCsn (.cv u)))
  let syntaxFormula0028 : Wff :=
    (.classEq (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      syntaxClass0027)
  let syntaxFormula0029 : Wff :=
    (.classMem (synCfv H (.cv y)) (synCin E (synCima (synCcnv S) (synCsn (.cv u)))))
  let syntaxFormula0030 : Wff :=
    (.classMem (synCop (.cv x) (.cv u)) (synCun H (synCsn (synCop (.cv x) (.cv u)))))
  let syntaxFormula0031 : Wff :=
    (.classEq (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv x)) (.cv u))
  let syntaxFormula0032 : Wff := (.imp syntaxFormula0030 syntaxFormula0031)
  let syntaxFormula0033 : Wff := (synWo syntaxFormula0013 (.classEq (.cv z) (.cv x)))
  let syntaxFormula0034 : Wff := (synWa syntaxFormula0010 (.classEq (.cv y) (.cv x)))
  let syntaxFormula0035 : Wff := (synWa syntaxFormula0034 syntaxFormula0013)
  let syntaxFormula0036 : Wff := (synWa syntaxFormula0035 (synWbr (.cv x) R (.cv z)))
  let syntaxFormula0037 : Wff :=
    (synWa (.classMem (.cv z) D) (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x)))))
  let syntaxFormula0038 : Wff := (synWa syntaxFormula0026 syntaxFormula0013)
  let syntaxFormula0039 : Wff :=
    (.classMem (synCfv H (.cv z))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  let syntaxFormula0040 : Wff := (.classMem (synCfv H (.cv z)) syntaxClass0027)
  let syntaxFormula0041 : Wff :=
    (.classMem (synCfv H (.cv z)) (synCin E (synCima (synCcnv S) (synCsn (.cv u)))))
  let syntaxFormula0042 : Wff :=
    (synWa syntaxFormula0041 (.neg (.classMem (synCfv H (.cv z)) (synCsn (.cv u)))))
  let syntaxFormula0043 : Wff :=
    (synWa syntaxFormula0035 (synWbr (.cv u) S (synCfv H (.cv z))))
  let syntaxFormula0044 : Wff :=
    (synWa (.classMem (synCfv H (.cv z)) E)
      (.classMem (synCfv H (.cv z)) (synCima (synCcnv S) (synCsn (.cv u)))))
  let syntaxFormula0045 : Wff := (synWa syntaxFormula0034 (.classEq (.cv z) (.cv x)))
  let syntaxFormula0046 : Wff := (synWral z syntaxClass0004 syntaxFormula0023)
  let syntaxFormula0047 : Wff := (synWral y syntaxClass0004 syntaxFormula0046)
  have p0000 := @gSimpl syntaxFormula0000 syntaxFormula0001
  have p0001 :=
    @gSimpr (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
  have p0002 :=
    @gSyl syntaxFormula0002 syntaxFormula0000
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) p0000 p0001
  have p0003 := @gSimpr syntaxFormula0000 syntaxFormula0001
  have p0004 :=
    @gJca syntaxFormula0002 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      syntaxFormula0001 p0002 p0003
  have p0005 := @gWecutisoaddpairf1ondv x u D R S E H
  have p0006 := @gSyl syntaxFormula0002 syntaxFormula0003 syntaxFormula0006 p0004 p0005
  have p0007 := @gSimpl syntaxFormula0012 syntaxFormula0013
  have p0008 := @gSimpl syntaxFormula0010 syntaxFormula0011
  have p0009 := @gSyl syntaxFormula0014 syntaxFormula0012 syntaxFormula0010 p0007 p0008
  have p0010 := @gSimpl syntaxFormula0008 syntaxFormula0009
  have p0011 := @gSimpl syntaxFormula0002 syntaxFormula0007
  have p0012 := @gSyl syntaxFormula0010 syntaxFormula0008 syntaxFormula0002 p0010 p0011
  have p0013 := @gSyl syntaxFormula0014 syntaxFormula0010 syntaxFormula0002 p0009 p0012
  have p0015 := @gSyl syntaxFormula0014 syntaxFormula0002 syntaxFormula0001 p0013 p0003
  have p0017 := @gSimpr syntaxFormula0010 syntaxFormula0011
  have p0018 := @gSyl syntaxFormula0014 syntaxFormula0012 syntaxFormula0011 p0007 p0017
  have p0019 := @gSimpr syntaxFormula0012 syntaxFormula0013
  have p0020 := @gJca syntaxFormula0014 syntaxFormula0011 syntaxFormula0013 p0018 p0019
  have p0021 := @gJca syntaxFormula0014 syntaxFormula0001 syntaxFormula0015 p0015 p0020
  have p0022 :=
    @gIsorel (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv y)
      (.cv z) R S H
  have p0023 :=
    @gSyl syntaxFormula0014 (synWa syntaxFormula0001 syntaxFormula0015)
      (synWb (synWbr (.cv y) R (.cv z)) (synWbr (synCfv H (.cv y)) S (synCfv H (.cv z))))
      p0021 p0022
  have p0037 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0038 :=
    @gSyl syntaxFormula0002 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (.classMem (.cv x) D) p0002 p0037
  have p0039 := @gElex (.cv x) D
  have p0040 :=
    @gSyl syntaxFormula0002 (.classMem (.cv x) D) (.classMem (.cv x) (synCvv)) p0038
      p0039
  have p0041 :=
    @gSyl syntaxFormula0014 syntaxFormula0002 (.classMem (.cv x) (synCvv)) p0013 p0040
  have p0042 := @gStrictsegdifiniclndv (.cv x) D R
  have p0043 :=
    @gSyl syntaxFormula0014 (.classMem (.cv x) (synCvv)) syntaxFormula0017 p0041 p0042
  have p0044 :=
    @gEleq2d syntaxFormula0014
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      syntaxClass0016 (.cv y) p0043
  have p0045 := @gMpbid syntaxFormula0014 syntaxFormula0011 syntaxFormula0018 p0018 p0044
  have p0046 :=
    @gEldif (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
      (synCsn (.cv x))
  have p0047 := @gSylib syntaxFormula0014 syntaxFormula0018 syntaxFormula0019 p0045 p0046
  have p0048 :=
    @gSimpr (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.neg (.classMem (.cv y) (synCsn (.cv x))))
  have p0049 :=
    @gSyl syntaxFormula0014 syntaxFormula0019
      (.neg (.classMem (.cv y) (synCsn (.cv x)))) p0047 p0048
  have p0065 := @gElsnc2g (.cv y) (.cv x) (synCvv)
  have p0066 :=
    @gSyl syntaxFormula0014 (.classMem (.cv x) (synCvv))
      (synWb (.classMem (.cv y) (synCsn (.cv x))) (.classEq (.cv y) (.cv x))) p0041
      p0065
  have p0067 :=
    @gNotbid syntaxFormula0014 (.classMem (.cv y) (synCsn (.cv x)))
      (.classEq (.cv y) (.cv x)) p0066
  have p0068 := (Nominal.biimpRefl (synWne (.cv y) (.cv x)))
  have p0069 :=
    @gA1i (synWb (synWne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))))
      syntaxFormula0014 p0068
  have p0070 :=
    @gBitr4d syntaxFormula0014 (.neg (.classMem (.cv y) (synCsn (.cv x))))
      (.neg (.classEq (.cv y) (.cv x))) (synWne (.cv y) (.cv x)) p0067 p0069
  have p0071 :=
    @gMpbid syntaxFormula0014 (.neg (.classMem (.cv y) (synCsn (.cv x))))
      (synWne (.cv y) (.cv x)) p0049 p0070
  have p0072 := @gNecomd syntaxFormula0014 (.cv y) (.cv x) p0071
  have p0073 := @gFvunsn H (.cv x) (.cv u) (.cv y)
  have p0074 :=
    @gSyl syntaxFormula0014 (synWne (.cv x) (.cv y))
      (.classEq (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y))
        (synCfv H (.cv y)))
      p0072 p0073
  have p0093 :=
    @gEleq2d syntaxFormula0014
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      syntaxClass0016 (.cv z) p0043
  have p0094 := @gMpbid syntaxFormula0014 syntaxFormula0013 syntaxFormula0020 p0019 p0093
  have p0095 :=
    @gEldif (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
      (synCsn (.cv x))
  have p0096 := @gSylib syntaxFormula0014 syntaxFormula0020 syntaxFormula0021 p0094 p0095
  have p0097 :=
    @gSimpr (.classMem (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.neg (.classMem (.cv z) (synCsn (.cv x))))
  have p0098 :=
    @gSyl syntaxFormula0014 syntaxFormula0021
      (.neg (.classMem (.cv z) (synCsn (.cv x)))) p0096 p0097
  have p0114 := @gElsnc2g (.cv z) (.cv x) (synCvv)
  have p0115 :=
    @gSyl syntaxFormula0014 (.classMem (.cv x) (synCvv))
      (synWb (.classMem (.cv z) (synCsn (.cv x))) (.classEq (.cv z) (.cv x))) p0041
      p0114
  have p0116 :=
    @gNotbid syntaxFormula0014 (.classMem (.cv z) (synCsn (.cv x)))
      (.classEq (.cv z) (.cv x)) p0115
  have p0117 := (Nominal.biimpRefl (synWne (.cv z) (.cv x)))
  have p0118 :=
    @gA1i (synWb (synWne (.cv z) (.cv x)) (.neg (.classEq (.cv z) (.cv x))))
      syntaxFormula0014 p0117
  have p0119 :=
    @gBitr4d syntaxFormula0014 (.neg (.classMem (.cv z) (synCsn (.cv x))))
      (.neg (.classEq (.cv z) (.cv x))) (synWne (.cv z) (.cv x)) p0116 p0118
  have p0120 :=
    @gMpbid syntaxFormula0014 (.neg (.classMem (.cv z) (synCsn (.cv x))))
      (synWne (.cv z) (.cv x)) p0098 p0119
  have p0121 := @gNecomd syntaxFormula0014 (.cv z) (.cv x) p0120
  have p0122 := @gFvunsn H (.cv x) (.cv u) (.cv z)
  have p0123 :=
    @gSyl syntaxFormula0014 (synWne (.cv x) (.cv z))
      (.classEq (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z))
        (synCfv H (.cv z)))
      p0121 p0122
  have p0124 :=
    @gBreq12d syntaxFormula0014
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y))
      (synCfv H (.cv y))
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z))
      (synCfv H (.cv z)) S p0074 p0123
  have p0125 :=
    @gBitr4d syntaxFormula0014 (synWbr (.cv y) R (.cv z))
      (synWbr (synCfv H (.cv y)) S (synCfv H (.cv z))) syntaxFormula0022 p0023 p0124
  have p0126 := @gEx syntaxFormula0012 syntaxFormula0013 syntaxFormula0023 p0125
  have p0127 := @gSimpl syntaxFormula0012 (.classEq (.cv z) (.cv x))
  have p0129 := @gSyl syntaxFormula0024 syntaxFormula0012 syntaxFormula0011 p0127 p0017
  have p0132 := @gSyl syntaxFormula0024 syntaxFormula0012 syntaxFormula0010 p0127 p0008
  have p0136 := @gSyl syntaxFormula0024 syntaxFormula0010 syntaxFormula0002 p0132 p0012
  have p0144 :=
    @gSyl syntaxFormula0024 syntaxFormula0002 (.classMem (.cv x) (synCvv)) p0136 p0040
  have p0146 :=
    @gSyl syntaxFormula0024 (.classMem (.cv x) (synCvv)) syntaxFormula0017 p0144 p0042
  have p0147 :=
    @gEleq2d syntaxFormula0024
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      syntaxClass0016 (.cv y) p0146
  have p0148 := @gMpbid syntaxFormula0024 syntaxFormula0011 syntaxFormula0018 p0129 p0147
  have p0150 := @gSylib syntaxFormula0024 syntaxFormula0018 syntaxFormula0019 p0148 p0046
  have p0151 :=
    @gSimpl (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.neg (.classMem (.cv y) (synCsn (.cv x))))
  have p0152 :=
    @gSyl syntaxFormula0024 syntaxFormula0019
      (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))) p0150
      p0151
  have p0153 := @gElin (.cv y) D (synCima (synCcnv R) (synCsn (.cv x)))
  have p0154 :=
    @gSylib syntaxFormula0024
      (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x)))))
      p0152 p0153
  have p0155 :=
    @gSimpr (.classMem (.cv y) D)
      (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x))))
  have p0156 :=
    @gSyl syntaxFormula0024
      (synWa (.classMem (.cv y) D)
        (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x)))))
      (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x)))) p0154 p0155
  have p0157 := @gEliniseg R (.cv x) (.cv y)
  have p0158 :=
    @gSylib syntaxFormula0024
      (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x))))
      (synWbr (.cv y) R (.cv x)) p0156 p0157
  have p0159 := @gSimpr syntaxFormula0012 (.classEq (.cv z) (.cv x))
  have p0160 := @gBreq2d syntaxFormula0024 (.cv z) (.cv x) (.cv y) R p0159
  have p0161 :=
    @gMpbird syntaxFormula0024 (synWbr (.cv y) R (.cv z)) (synWbr (.cv y) R (.cv x))
      p0158 p0160
  have p0170 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S H
  have p0171 := @gSyl syntaxFormula0002 syntaxFormula0001 syntaxFormula0025 p0003 p0170
  have p0172 :=
    @gF1of (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) H
  have p0173 := @gSyl syntaxFormula0002 syntaxFormula0025 syntaxFormula0026 p0171 p0172
  have p0174 := @gSyl syntaxFormula0024 syntaxFormula0002 syntaxFormula0026 p0136 p0173
  have p0178 := @gJca syntaxFormula0024 syntaxFormula0026 syntaxFormula0011 p0174 p0129
  have p0179 :=
    @gFfvelrn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv y) H
  have p0180 :=
    @gSyl syntaxFormula0024 (synWa syntaxFormula0026 syntaxFormula0011)
      (.classMem (synCfv H (.cv y))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0178 p0179
  have p0191 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0192 :=
    @gSyl syntaxFormula0002 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (.classMem (.cv u) E) p0002 p0191
  have p0193 := @gElex (.cv u) E
  have p0194 :=
    @gSyl syntaxFormula0002 (.classMem (.cv u) E) (.classMem (.cv u) (synCvv)) p0192
      p0193
  have p0195 :=
    @gSyl syntaxFormula0024 syntaxFormula0002 (.classMem (.cv u) (synCvv)) p0136 p0194
  have p0196 := @gStrictsegdifiniclndv (.cv u) E S
  have p0197 :=
    @gSyl syntaxFormula0024 (.classMem (.cv u) (synCvv)) syntaxFormula0028 p0195 p0196
  have p0198 :=
    @gEleq2d syntaxFormula0024
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      syntaxClass0027 (synCfv H (.cv y)) p0197
  have p0199 :=
    @gMpbid syntaxFormula0024
      (.classMem (synCfv H (.cv y))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classMem (synCfv H (.cv y)) syntaxClass0027) p0180 p0198
  have p0200 :=
    @gEldif (synCfv H (.cv y)) (synCin E (synCima (synCcnv S) (synCsn (.cv u))))
      (synCsn (.cv u))
  have p0201 :=
    @gSylib syntaxFormula0024 (.classMem (synCfv H (.cv y)) syntaxClass0027)
      (synWa syntaxFormula0029 (.neg (.classMem (synCfv H (.cv y)) (synCsn (.cv u)))))
      p0199 p0200
  have p0202 :=
    @gSimpl syntaxFormula0029 (.neg (.classMem (synCfv H (.cv y)) (synCsn (.cv u))))
  have p0203 :=
    @gSyl syntaxFormula0024
      (synWa syntaxFormula0029 (.neg (.classMem (synCfv H (.cv y)) (synCsn (.cv u)))))
      syntaxFormula0029 p0201 p0202
  have p0204 := @gElin (synCfv H (.cv y)) E (synCima (synCcnv S) (synCsn (.cv u)))
  have p0205 :=
    @gSylib syntaxFormula0024 syntaxFormula0029
      (synWa (.classMem (synCfv H (.cv y)) E)
        (.classMem (synCfv H (.cv y)) (synCima (synCcnv S) (synCsn (.cv u)))))
      p0203 p0204
  have p0206 :=
    @gSimpr (.classMem (synCfv H (.cv y)) E)
      (.classMem (synCfv H (.cv y)) (synCima (synCcnv S) (synCsn (.cv u))))
  have p0207 :=
    @gSyl syntaxFormula0024
      (synWa (.classMem (synCfv H (.cv y)) E)
        (.classMem (synCfv H (.cv y)) (synCima (synCcnv S) (synCsn (.cv u)))))
      (.classMem (synCfv H (.cv y)) (synCima (synCcnv S) (synCsn (.cv u)))) p0205
      p0206
  have p0208 := @gEliniseg S (.cv u) (synCfv H (.cv y))
  have p0209 :=
    @gSylib syntaxFormula0024
      (.classMem (synCfv H (.cv y)) (synCima (synCcnv S) (synCsn (.cv u))))
      (synWbr (synCfv H (.cv y)) S (.cv u)) p0207 p0208
  have p0235 :=
    @gSyl syntaxFormula0024 syntaxFormula0019
      (.neg (.classMem (.cv y) (synCsn (.cv x)))) p0150 p0048
  have p0252 :=
    @gSyl syntaxFormula0024 (.classMem (.cv x) (synCvv))
      (synWb (.classMem (.cv y) (synCsn (.cv x))) (.classEq (.cv y) (.cv x))) p0144
      p0065
  have p0253 :=
    @gNotbid syntaxFormula0024 (.classMem (.cv y) (synCsn (.cv x)))
      (.classEq (.cv y) (.cv x)) p0252
  have p0255 :=
    @gA1i (synWb (synWne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))))
      syntaxFormula0024 p0068
  have p0256 :=
    @gBitr4d syntaxFormula0024 (.neg (.classMem (.cv y) (synCsn (.cv x))))
      (.neg (.classEq (.cv y) (.cv x))) (synWne (.cv y) (.cv x)) p0253 p0255
  have p0257 :=
    @gMpbid syntaxFormula0024 (.neg (.classMem (.cv y) (synCsn (.cv x))))
      (synWne (.cv y) (.cv x)) p0235 p0256
  have p0258 := @gNecomd syntaxFormula0024 (.cv y) (.cv x) p0257
  have p0260 :=
    @gSyl syntaxFormula0024 (synWne (.cv x) (.cv y))
      (.classEq (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y))
        (synCfv H (.cv y)))
      p0258 p0073
  have p0262 :=
    @gFveq2d syntaxFormula0024 (.cv z) (.cv x)
      (synCun H (synCsn (synCop (.cv x) (.cv u)))) p0159
  have p0273 := @gOpexg (.cv x) (.cv u) D E
  have p0274 :=
    @gSyl syntaxFormula0002 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (.classMem (synCop (.cv x) (.cv u)) (synCvv)) p0002 p0273
  have p0275 := @gSnidg (synCop (.cv x) (.cv u)) (synCvv)
  have p0276 :=
    @gSyl syntaxFormula0002 (.classMem (synCop (.cv x) (.cv u)) (synCvv))
      (.classMem (synCop (.cv x) (.cv u)) (synCsn (synCop (.cv x) (.cv u)))) p0274
      p0275
  have p0277 := @gElun2 (synCop (.cv x) (.cv u)) (synCsn (synCop (.cv x) (.cv u))) H
  have p0278 :=
    @gSyl syntaxFormula0002
      (.classMem (synCop (.cv x) (.cv u)) (synCsn (synCop (.cv x) (.cv u))))
      syntaxFormula0030 p0276 p0277
  have p0286 :=
    @gF1ofun syntaxClass0004 syntaxClass0005
      (synCun H (synCsn (synCop (.cv x) (.cv u))))
  have p0287 :=
    @gSyl syntaxFormula0002 syntaxFormula0006
      (synWfun (synCun H (synCsn (synCop (.cv x) (.cv u))))) p0006 p0286
  have p0288 := @gFunopfv (.cv x) (.cv u) (synCun H (synCsn (synCop (.cv x) (.cv u))))
  have p0289 :=
    @gSyl syntaxFormula0002 (synWfun (synCun H (synCsn (synCop (.cv x) (.cv u)))))
      syntaxFormula0032 p0287 p0288
  have p0290 := @gMpd syntaxFormula0002 syntaxFormula0030 syntaxFormula0031 p0278 p0289
  have p0291 := @gSyl syntaxFormula0024 syntaxFormula0002 syntaxFormula0031 p0136 p0290
  have p0292 :=
    @gEqtrd syntaxFormula0024
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z))
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0262
      p0291
  have p0293 :=
    @gBreq12d syntaxFormula0024
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y))
      (synCfv H (.cv y))
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z)) (.cv u) S p0260
      p0292
  have p0294 :=
    @gMpbird syntaxFormula0024 syntaxFormula0022 (synWbr (synCfv H (.cv y)) S (.cv u))
      p0209 p0293
  have p0295 :=
    @gN2thd syntaxFormula0024 (synWbr (.cv y) R (.cv z)) syntaxFormula0022 p0161 p0294
  have p0296 := @gEx syntaxFormula0012 (.classEq (.cv z) (.cv x)) syntaxFormula0023 p0295
  have p0298 := @gSimpr syntaxFormula0008 syntaxFormula0009
  have p0299 :=
    @gElun (.cv z)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCsn (.cv x))
  have p0300 := @gElsn z (.cv x) dv_cache_0001
  have p0301 :=
    @gOrbi2i (.classMem (.cv z) (synCsn (.cv x))) (.classEq (.cv z) (.cv x))
      syntaxFormula0013 p0300
  have p0302 :=
    @gBitri syntaxFormula0009
      (synWo syntaxFormula0013 (.classMem (.cv z) (synCsn (.cv x)))) syntaxFormula0033
      p0299 p0301
  have p0303 := @gSylib syntaxFormula0010 syntaxFormula0009 syntaxFormula0033 p0298 p0302
  have p0304 := @gSyl syntaxFormula0012 syntaxFormula0010 syntaxFormula0033 p0008 p0303
  have p0305 :=
    @gMpjaod syntaxFormula0012 syntaxFormula0013 syntaxFormula0023
      (.classEq (.cv z) (.cv x)) p0126 p0296 p0304
  have p0306 := @gEx syntaxFormula0010 syntaxFormula0011 syntaxFormula0023 p0305
  have p0307 := @gSimpr syntaxFormula0034 syntaxFormula0013
  have p0308 := @gSimpl syntaxFormula0034 syntaxFormula0013
  have p0309 := @gSimpl syntaxFormula0010 (.classEq (.cv y) (.cv x))
  have p0310 := @gSyl syntaxFormula0035 syntaxFormula0034 syntaxFormula0010 p0308 p0309
  have p0314 := @gSyl syntaxFormula0035 syntaxFormula0010 syntaxFormula0002 p0310 p0012
  have p0322 :=
    @gSyl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv x) (synCvv)) p0314 p0040
  have p0324 :=
    @gSyl syntaxFormula0035 (.classMem (.cv x) (synCvv)) syntaxFormula0017 p0322 p0042
  have p0325 :=
    @gEleq2d syntaxFormula0035
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      syntaxClass0016 (.cv z) p0324
  have p0326 := @gMpbid syntaxFormula0035 syntaxFormula0013 syntaxFormula0020 p0307 p0325
  have p0328 := @gSylib syntaxFormula0035 syntaxFormula0020 syntaxFormula0021 p0326 p0095
  have p0330 :=
    @gSyl syntaxFormula0035 syntaxFormula0021
      (.neg (.classMem (.cv z) (synCsn (.cv x)))) p0328 p0097
  have p0347 :=
    @gSyl syntaxFormula0035 (.classMem (.cv x) (synCvv))
      (synWb (.classMem (.cv z) (synCsn (.cv x))) (.classEq (.cv z) (.cv x))) p0322
      p0114
  have p0348 :=
    @gNotbid syntaxFormula0035 (.classMem (.cv z) (synCsn (.cv x)))
      (.classEq (.cv z) (.cv x)) p0347
  have p0350 :=
    @gA1i (synWb (synWne (.cv z) (.cv x)) (.neg (.classEq (.cv z) (.cv x))))
      syntaxFormula0035 p0117
  have p0351 :=
    @gBitr4d syntaxFormula0035 (.neg (.classMem (.cv z) (synCsn (.cv x))))
      (.neg (.classEq (.cv z) (.cv x))) (synWne (.cv z) (.cv x)) p0348 p0350
  have p0352 :=
    @gMpbid syntaxFormula0035 (.neg (.classMem (.cv z) (synCsn (.cv x))))
      (synWne (.cv z) (.cv x)) p0330 p0351
  have p0353 := @gSimpl syntaxFormula0035 (synWbr (.cv x) R (.cv z))
  have p0362 :=
    @gSimpl (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
  have p0363 :=
    @gSyl syntaxFormula0002 syntaxFormula0000
      (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E)) p0000 p0362
  have p0364 := @gSimpl (synWbr R (synCwe) D) (synWbr S (synCwe) E)
  have p0365 :=
    @gSyl syntaxFormula0002 (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
      (synWbr R (synCwe) D) p0363 p0364
  have p0366 := @gWppweantisym D R
  have p0367 :=
    @gSyl syntaxFormula0002 (synWbr R (synCwe) D) (synWbr R (synCantisym) D) p0365
      p0366
  have p0368 :=
    @gSyl syntaxFormula0035 syntaxFormula0002 (synWbr R (synCantisym) D) p0314 p0367
  have p0369 :=
    @gSyl syntaxFormula0036 syntaxFormula0035 (synWbr R (synCantisym) D) p0353 p0368
  have p0393 :=
    @gSimpl (.classMem (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.neg (.classMem (.cv z) (synCsn (.cv x))))
  have p0394 :=
    @gSyl syntaxFormula0035 syntaxFormula0021
      (.classMem (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))) p0328
      p0393
  have p0395 := @gElin (.cv z) D (synCima (synCcnv R) (synCsn (.cv x)))
  have p0396 :=
    @gSylib syntaxFormula0035
      (.classMem (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      syntaxFormula0037 p0394 p0395
  have p0397 :=
    @gSimpl (.classMem (.cv z) D)
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
  have p0398 :=
    @gSyl syntaxFormula0035 syntaxFormula0037 (.classMem (.cv z) D) p0396 p0397
  have p0399 :=
    @gSyl syntaxFormula0036 syntaxFormula0035 (.classMem (.cv z) D) p0353 p0398
  have p0413 :=
    @gSyl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv x) D) p0314 p0038
  have p0414 :=
    @gSyl syntaxFormula0036 syntaxFormula0035 (.classMem (.cv x) D) p0353 p0413
  have p0442 :=
    @gSimpr (.classMem (.cv z) D)
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
  have p0443 :=
    @gSyl syntaxFormula0035 syntaxFormula0037
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x)))) p0396 p0442
  have p0444 := @gEliniseg R (.cv x) (.cv z)
  have p0445 :=
    @gSylib syntaxFormula0035
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
      (synWbr (.cv z) R (.cv x)) p0443 p0444
  have p0446 :=
    @gSyl syntaxFormula0036 syntaxFormula0035 (synWbr (.cv z) R (.cv x)) p0353 p0445
  have p0447 := @gSimpr syntaxFormula0035 (synWbr (.cv x) R (.cv z))
  have p0448 :=
    @gAntid syntaxFormula0036 D R (.cv z) (.cv x) p0369 p0399 p0414 p0446 p0447
  have p0449 :=
    @gEx syntaxFormula0035 (synWbr (.cv x) R (.cv z)) (.classEq (.cv z) (.cv x)) p0448
  have p0450 :=
    @gNecon3ad syntaxFormula0035 (synWbr (.cv x) R (.cv z)) (.cv z) (.cv x) p0449
  have p0451 :=
    @gMpd syntaxFormula0035 (synWne (.cv z) (.cv x)) (.neg (synWbr (.cv x) R (.cv z)))
      p0352 p0450
  have p0453 := @gSimpr syntaxFormula0010 (.classEq (.cv y) (.cv x))
  have p0454 :=
    @gSyl syntaxFormula0035 syntaxFormula0034 (.classEq (.cv y) (.cv x)) p0308 p0453
  have p0455 := @gBreq1d syntaxFormula0035 (.cv y) (.cv x) (.cv z) R p0454
  have p0456 :=
    @gNotbid syntaxFormula0035 (synWbr (.cv y) R (.cv z)) (synWbr (.cv x) R (.cv z))
      p0455
  have p0457 :=
    @gMpbird syntaxFormula0035 (.neg (synWbr (.cv y) R (.cv z)))
      (.neg (synWbr (.cv x) R (.cv z))) p0451 p0456
  have p0470 := @gSyl syntaxFormula0035 syntaxFormula0002 syntaxFormula0026 p0314 p0173
  have p0472 := @gJca syntaxFormula0035 syntaxFormula0026 syntaxFormula0013 p0470 p0307
  have p0473 :=
    @gFfvelrn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv z) H
  have p0474 := @gSyl syntaxFormula0035 syntaxFormula0038 syntaxFormula0039 p0472 p0473
  have p0489 :=
    @gSyl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv u) (synCvv)) p0314 p0194
  have p0491 :=
    @gSyl syntaxFormula0035 (.classMem (.cv u) (synCvv)) syntaxFormula0028 p0489 p0196
  have p0492 :=
    @gEleq2d syntaxFormula0035
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      syntaxClass0027 (synCfv H (.cv z)) p0491
  have p0493 := @gMpbid syntaxFormula0035 syntaxFormula0039 syntaxFormula0040 p0474 p0492
  have p0494 :=
    @gEldif (synCfv H (.cv z)) (synCin E (synCima (synCcnv S) (synCsn (.cv u))))
      (synCsn (.cv u))
  have p0495 := @gSylib syntaxFormula0035 syntaxFormula0040 syntaxFormula0042 p0493 p0494
  have p0496 :=
    @gSimpr syntaxFormula0041 (.neg (.classMem (synCfv H (.cv z)) (synCsn (.cv u))))
  have p0497 :=
    @gSyl syntaxFormula0035 syntaxFormula0042
      (.neg (.classMem (synCfv H (.cv z)) (synCsn (.cv u)))) p0495 p0496
  have p0513 := @gElsnc2g (synCfv H (.cv z)) (.cv u) (synCvv)
  have p0514 :=
    @gSyl syntaxFormula0035 (.classMem (.cv u) (synCvv))
      (synWb (.classMem (synCfv H (.cv z)) (synCsn (.cv u)))
        (.classEq (synCfv H (.cv z)) (.cv u)))
      p0489 p0513
  have p0515 :=
    @gNotbid syntaxFormula0035 (.classMem (synCfv H (.cv z)) (synCsn (.cv u)))
      (.classEq (synCfv H (.cv z)) (.cv u)) p0514
  have p0516 := (Nominal.biimpRefl (synWne (synCfv H (.cv z)) (.cv u)))
  have p0517 :=
    @gA1i
      (synWb (synWne (synCfv H (.cv z)) (.cv u))
        (.neg (.classEq (synCfv H (.cv z)) (.cv u))))
      syntaxFormula0035 p0516
  have p0518 :=
    @gBitr4d syntaxFormula0035 (.neg (.classMem (synCfv H (.cv z)) (synCsn (.cv u))))
      (.neg (.classEq (synCfv H (.cv z)) (.cv u))) (synWne (synCfv H (.cv z)) (.cv u))
      p0515 p0517
  have p0519 :=
    @gMpbid syntaxFormula0035 (.neg (.classMem (synCfv H (.cv z)) (synCsn (.cv u))))
      (synWne (synCfv H (.cv z)) (.cv u)) p0497 p0518
  have p0520 := @gSimpl syntaxFormula0035 (synWbr (.cv u) S (synCfv H (.cv z)))
  have p0531 := @gSimpr (synWbr R (synCwe) D) (synWbr S (synCwe) E)
  have p0532 :=
    @gSyl syntaxFormula0002 (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
      (synWbr S (synCwe) E) p0363 p0531
  have p0533 := @gWppweantisym E S
  have p0534 :=
    @gSyl syntaxFormula0002 (synWbr S (synCwe) E) (synWbr S (synCantisym) E) p0532
      p0533
  have p0535 :=
    @gSyl syntaxFormula0035 syntaxFormula0002 (synWbr S (synCantisym) E) p0314 p0534
  have p0536 :=
    @gSyl syntaxFormula0043 syntaxFormula0035 (synWbr S (synCantisym) E) p0520 p0535
  have p0576 :=
    @gSimpl syntaxFormula0041 (.neg (.classMem (synCfv H (.cv z)) (synCsn (.cv u))))
  have p0577 := @gSyl syntaxFormula0035 syntaxFormula0042 syntaxFormula0041 p0495 p0576
  have p0578 := @gElin (synCfv H (.cv z)) E (synCima (synCcnv S) (synCsn (.cv u)))
  have p0579 := @gSylib syntaxFormula0035 syntaxFormula0041 syntaxFormula0044 p0577 p0578
  have p0580 :=
    @gSimpl (.classMem (synCfv H (.cv z)) E)
      (.classMem (synCfv H (.cv z)) (synCima (synCcnv S) (synCsn (.cv u))))
  have p0581 :=
    @gSyl syntaxFormula0035 syntaxFormula0044 (.classMem (synCfv H (.cv z)) E) p0579
      p0580
  have p0582 :=
    @gSyl syntaxFormula0043 syntaxFormula0035 (.classMem (synCfv H (.cv z)) E) p0520
      p0581
  have p0596 :=
    @gSyl syntaxFormula0035 syntaxFormula0002 (.classMem (.cv u) E) p0314 p0192
  have p0597 :=
    @gSyl syntaxFormula0043 syntaxFormula0035 (.classMem (.cv u) E) p0520 p0596
  have p0641 :=
    @gSimpr (.classMem (synCfv H (.cv z)) E)
      (.classMem (synCfv H (.cv z)) (synCima (synCcnv S) (synCsn (.cv u))))
  have p0642 :=
    @gSyl syntaxFormula0035 syntaxFormula0044
      (.classMem (synCfv H (.cv z)) (synCima (synCcnv S) (synCsn (.cv u)))) p0579
      p0641
  have p0643 := @gEliniseg S (.cv u) (synCfv H (.cv z))
  have p0644 :=
    @gSylib syntaxFormula0035
      (.classMem (synCfv H (.cv z)) (synCima (synCcnv S) (synCsn (.cv u))))
      (synWbr (synCfv H (.cv z)) S (.cv u)) p0642 p0643
  have p0645 :=
    @gSyl syntaxFormula0043 syntaxFormula0035 (synWbr (synCfv H (.cv z)) S (.cv u))
      p0520 p0644
  have p0646 := @gSimpr syntaxFormula0035 (synWbr (.cv u) S (synCfv H (.cv z)))
  have p0647 :=
    @gAntid syntaxFormula0043 E S (synCfv H (.cv z)) (.cv u) p0536 p0582 p0597 p0645
      p0646
  have p0648 :=
    @gEx syntaxFormula0035 (synWbr (.cv u) S (synCfv H (.cv z)))
      (.classEq (synCfv H (.cv z)) (.cv u)) p0647
  have p0649 :=
    @gNecon3ad syntaxFormula0035 (synWbr (.cv u) S (synCfv H (.cv z)))
      (synCfv H (.cv z)) (.cv u) p0648
  have p0650 :=
    @gMpd syntaxFormula0035 (synWne (synCfv H (.cv z)) (.cv u))
      (.neg (synWbr (.cv u) S (synCfv H (.cv z)))) p0519 p0649
  have p0654 :=
    @gFveq2d syntaxFormula0035 (.cv y) (.cv x)
      (synCun H (synCsn (synCop (.cv x) (.cv u)))) p0454
  have p0683 := @gSyl syntaxFormula0035 syntaxFormula0002 syntaxFormula0031 p0314 p0290
  have p0684 :=
    @gEqtrd syntaxFormula0035
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y))
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0654
      p0683
  have p0731 := @gNecomd syntaxFormula0035 (.cv z) (.cv x) p0352
  have p0733 :=
    @gSyl syntaxFormula0035 (synWne (.cv x) (.cv z))
      (.classEq (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z))
        (synCfv H (.cv z)))
      p0731 p0122
  have p0734 :=
    @gBreq12d syntaxFormula0035
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y)) (.cv u)
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z))
      (synCfv H (.cv z)) S p0684 p0733
  have p0735 :=
    @gNotbid syntaxFormula0035 syntaxFormula0022 (synWbr (.cv u) S (synCfv H (.cv z)))
      p0734
  have p0736 :=
    @gMpbird syntaxFormula0035 (.neg syntaxFormula0022)
      (.neg (synWbr (.cv u) S (synCfv H (.cv z)))) p0650 p0735
  have p0737 :=
    @gN2falsed syntaxFormula0035 (synWbr (.cv y) R (.cv z)) syntaxFormula0022 p0457
      p0736
  have p0738 := @gEx syntaxFormula0034 syntaxFormula0013 syntaxFormula0023 p0737
  have p0739 := @gSimpl syntaxFormula0034 (.classEq (.cv z) (.cv x))
  have p0741 := @gSyl syntaxFormula0045 syntaxFormula0034 syntaxFormula0010 p0739 p0309
  have p0745 := @gSyl syntaxFormula0045 syntaxFormula0010 syntaxFormula0002 p0741 p0012
  have p0751 := @gWppweref D R
  have p0752 :=
    @gSyl syntaxFormula0002 (synWbr R (synCwe) D) (synWbr R (synCref) D) p0365 p0751
  have p0758 := @gRefd syntaxFormula0002 D R (.cv x) p0752 p0038
  have p0759 :=
    @gSyl syntaxFormula0045 syntaxFormula0002 (synWbr (.cv x) R (.cv x)) p0745 p0758
  have p0762 :=
    @gSyl syntaxFormula0045 syntaxFormula0034 (.classEq (.cv y) (.cv x)) p0739 p0453
  have p0763 := @gSimpr syntaxFormula0034 (.classEq (.cv z) (.cv x))
  have p0764 := @gBreq12d syntaxFormula0045 (.cv y) (.cv x) (.cv z) (.cv x) R p0762 p0763
  have p0765 :=
    @gMpbird syntaxFormula0045 (synWbr (.cv y) R (.cv z)) (synWbr (.cv x) R (.cv x))
      p0759 p0764
  have p0778 := @gWppweref E S
  have p0779 :=
    @gSyl syntaxFormula0002 (synWbr S (synCwe) E) (synWbr S (synCref) E) p0532 p0778
  have p0785 := @gRefd syntaxFormula0002 E S (.cv u) p0779 p0192
  have p0786 :=
    @gSyl syntaxFormula0045 syntaxFormula0002 (synWbr (.cv u) S (.cv u)) p0745 p0785
  have p0790 :=
    @gFveq2d syntaxFormula0045 (.cv y) (.cv x)
      (synCun H (synCsn (synCop (.cv x) (.cv u)))) p0762
  have p0819 := @gSyl syntaxFormula0045 syntaxFormula0002 syntaxFormula0031 p0745 p0290
  have p0820 :=
    @gEqtrd syntaxFormula0045
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y))
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0790
      p0819
  have p0822 :=
    @gFveq2d syntaxFormula0045 (.cv z) (.cv x)
      (synCun H (synCsn (synCop (.cv x) (.cv u)))) p0763
  have p0852 :=
    @gEqtrd syntaxFormula0045
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z))
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv x)) (.cv u) p0822
      p0819
  have p0853 :=
    @gBreq12d syntaxFormula0045
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv y)) (.cv u)
      (synCfv (synCun H (synCsn (synCop (.cv x) (.cv u)))) (.cv z)) (.cv u) S p0820
      p0852
  have p0854 :=
    @gMpbird syntaxFormula0045 syntaxFormula0022 (synWbr (.cv u) S (.cv u)) p0786 p0853
  have p0855 :=
    @gN2thd syntaxFormula0045 (synWbr (.cv y) R (.cv z)) syntaxFormula0022 p0765 p0854
  have p0856 := @gEx syntaxFormula0034 (.classEq (.cv z) (.cv x)) syntaxFormula0023 p0855
  have p0864 := @gSyl syntaxFormula0034 syntaxFormula0010 syntaxFormula0033 p0309 p0303
  have p0865 :=
    @gMpjaod syntaxFormula0034 syntaxFormula0013 syntaxFormula0023
      (.classEq (.cv z) (.cv x)) p0738 p0856 p0864
  have p0866 := @gEx syntaxFormula0010 (.classEq (.cv y) (.cv x)) syntaxFormula0023 p0865
  have p0868 := @gSimpr syntaxFormula0002 syntaxFormula0007
  have p0869 := @gSyl syntaxFormula0010 syntaxFormula0008 syntaxFormula0007 p0010 p0868
  have p0870 :=
    @gElun (.cv y)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCsn (.cv x))
  have p0871 := @gElsn y (.cv x) dv_cache_0002
  have p0872 :=
    @gOrbi2i (.classMem (.cv y) (synCsn (.cv x))) (.classEq (.cv y) (.cv x))
      syntaxFormula0011 p0871
  have p0873 :=
    @gBitri syntaxFormula0007
      (synWo syntaxFormula0011 (.classMem (.cv y) (synCsn (.cv x))))
      (synWo syntaxFormula0011 (.classEq (.cv y) (.cv x))) p0870 p0872
  have p0874 :=
    @gSylib syntaxFormula0010 syntaxFormula0007
      (synWo syntaxFormula0011 (.classEq (.cv y) (.cv x))) p0869 p0873
  have p0875 :=
    @gMpjaod syntaxFormula0010 syntaxFormula0011 syntaxFormula0023
      (.classEq (.cv y) (.cv x)) p0306 p0866 p0874
  have p0876 :=
    @gRalrimiva syntaxFormula0008 syntaxFormula0023 z syntaxClass0004 dv_cache_0003 p0875
  have p0877 :=
    @gRalrimiva syntaxFormula0002 syntaxFormula0046 y syntaxClass0004 dv_cache_0004 p0876
  have p0878 := @gJca syntaxFormula0002 syntaxFormula0006 syntaxFormula0047 p0006 p0877
  have p0879 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso y z
      syntaxClass0004 syntaxClass0005 R S (synCun H (synCsn (synCop (.cv x) (.cv u))))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0880 :=
    @gSylibr syntaxFormula0002 (synWa syntaxFormula0006 syntaxFormula0047)
      (synWiso (synCun H (synCsn (synCop (.cv x) (.cv u)))) R S syntaxClass0004
        syntaxClass0005)
      p0878 p0879
  exact p0880


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wedifleastssndv`. -/
@[expose]
noncomputable def gWedifleastssndv (x : Var) (y : Var) (C : Class) (D : Class)
    (R : Class) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (_dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y)
    (hyp_wedifleastssndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wedifleastssndv_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.imp (synWrex x D (.neg (.classMem (.cv x) C))) (synWrex y D
          (synWa (.neg (.classMem (.cv y) C))
            (synWss (synCdif D C) (synCima R (synCsn (.cv y))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
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
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0004 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.neg (.classMem (.cv y) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWrex x D (.neg (.classMem (.cv x) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_y, (Ne.symm dv_x_y), dv_C_y, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synWrex x D (.neg (.classMem (.cv x) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_ne_x, fresh_z_not_C, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.neg (.classMem (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, or_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Wff.neg (.classMem (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.neg (.classMem (.cv z) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0016 : z ∉ ((Class.cv w)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0017 :
    z ∉ ((Wff.imp (.neg (.classMem (.cv w) C)) (synWbr (.cv y) R (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_C, fresh_z_ne_y, fresh_z_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((synCdif D C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          Finset.mem_union, fresh_w_not_D, fresh_w_not_C, or_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((synCima R (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_R, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0020 :
    w ∉
      ((synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_D, fresh_w_ne_z,
          fresh_w_not_C, fresh_w_ne_y, fresh_w_not_R, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gNotab (.classMem (.cv x) C) x
  have p0001 := @gAbid2 x C dv_cache_0001
  have p0002 := @gDifeq2i (.cab x (.classMem (.cv x) C)) C (synCvv) p0001
  have p0003 :=
    @gEqtri (.cab x (.neg (.classMem (.cv x) C)))
      (synCdif (synCvv) (.cab x (.classMem (.cv x) C))) (synCdif (synCvv) C) p0000
      p0002
  have p0004 := @gVvex
  have p0005 := @gDifex (synCvv) C p0004 hyp_wedifleastssndv_2
  have p0006 :=
    @gEqeltri (.cab x (.neg (.classMem (.cv x) C))) (synCdif (synCvv) C) (synCvv)
      p0003 p0005
  have p0007 := @gEleq1 (.cv x) (.cv y) C
  have p0008 :=
    @gNotbid (.classEq (.cv x) (.cv y)) (.classMem (.cv x) C) (.classMem (.cv y) C) p0007
  have p0009 := @gEleq1 (.cv x) (.cv z) C
  have p0010 :=
    @gNotbid (.classEq (.cv x) (.cv z)) (.classMem (.cv x) C) (.classMem (.cv z) C) p0009
  have p0011 :=
    @gA1i (synWbr R (synCwe) D) (synWrex x D (.neg (.classMem (.cv x) C)))
      hyp_wedifleastssndv_1
  have p0012 := @gId (synWrex x D (.neg (.classMem (.cv x) C)))
  have p0013_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv y) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0013_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (.neg (.classMem (.cv x) C)) (.neg (.classMem (.cv z) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0013 :=
    @gWeds (synWrex x D (.neg (.classMem (.cv x) C))) (.neg (.classMem (.cv x) C))
      (.neg (.classMem (.cv y) C)) (.neg (.classMem (.cv z) C)) x y z D R dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0006 p0013_e01_recanon p0013_e02_recanon p0011 p0012
  have p0014 :=
    @gSimpl (.neg (.classMem (.cv y) C))
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
  have p0015 :=
    @gSimpr (.neg (.classMem (.cv y) C))
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
  have p0016 :=
    @gSimpr
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
      (.classMem (.cv w) (synCdif D C))
  have p0017 := @gEldif (.cv w) D C
  have p0018 :=
    @gSylib
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (.classMem (.cv w) (synCdif D C))
      (synWa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) p0016 p0017
  have p0019 := @gSimpr (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))
  have p0020 :=
    @gSyl
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (synWa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C)))
      (.neg (.classMem (.cv w) C)) p0018 p0019
  have p0024 := @gSimpl (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))
  have p0025 :=
    @gSyl
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (synWa (.classMem (.cv w) D) (.neg (.classMem (.cv w) C))) (.classMem (.cv w) D)
      p0018 p0024
  have p0026 :=
    @gSimpl
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
      (.classMem (.cv w) (synCdif D C))
  have p0027 :=
    @gJca
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (.classMem (.cv w) D)
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))) p0025
      p0026
  have p0028 := @gEleq1 (.cv z) (.cv w) C
  have p0029 :=
    @gNotbid (.classEq (.cv z) (.cv w)) (.classMem (.cv z) C) (.classMem (.cv w) C) p0028
  have p0030 := @gBreq2 (.cv z) (.cv w) (.cv y) R
  have p0031 :=
    @gImbi12d (.classEq (.cv z) (.cv w)) (.neg (.classMem (.cv z) C))
      (.neg (.classMem (.cv w) C)) (synWbr (.cv y) R (.cv z)) (synWbr (.cv y) R (.cv w))
      p0029 p0030
  have p0032 :=
    @gRspcva (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))
      (.imp (.neg (.classMem (.cv w) C)) (synWbr (.cv y) R (.cv w))) z (.cv w) D
      dv_cache_0016 dv_cache_0004 dv_cache_0017 p0031
  have p0033 :=
    @gSyl
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (synWa (.classMem (.cv w) D)
        (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))))
      (.imp (.neg (.classMem (.cv w) C)) (synWbr (.cv y) R (.cv w))) p0027 p0032
  have p0034 :=
    @gMpd
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (.neg (.classMem (.cv w) C)) (synWbr (.cv y) R (.cv w)) p0020 p0033
  have p0035 := @gElimasn R (.cv y) (.cv w)
  have p0036 := (Nominal.biimpRefl (synWbr (.cv y) R (.cv w)))
  have p0037 :=
    @gBitr4i (.classMem (.cv w) (synCima R (synCsn (.cv y))))
      (.classMem (synCop (.cv y) (.cv w)) R) (synWbr (.cv y) R (.cv w)) p0035 p0036
  have p0038 :=
    @gSylibr
      (synWa (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
        (.classMem (.cv w) (synCdif D C)))
      (synWbr (.cv y) R (.cv w)) (.classMem (.cv w) (synCima R (synCsn (.cv y)))) p0034
      p0037
  have p0039 :=
    @gEx (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
      (.classMem (.cv w) (synCdif D C))
      (.classMem (.cv w) (synCima R (synCsn (.cv y)))) p0038
  have p0040 :=
    @gSsrdv
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))) w
      (synCdif D C) (synCima R (synCsn (.cv y))) dv_cache_0018 dv_cache_0019
      dv_cache_0020 p0039
  have p0041 :=
    @gSyl
      (synWa (.neg (.classMem (.cv y) C))
        (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))))
      (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))
      (synWss (synCdif D C) (synCima R (synCsn (.cv y)))) p0015 p0040
  have p0042 :=
    @gJca
      (synWa (.neg (.classMem (.cv y) C))
        (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))))
      (.neg (.classMem (.cv y) C)) (synWss (synCdif D C) (synCima R (synCsn (.cv y))))
      p0014 p0041
  have p0043 :=
    @gReximi
      (synWa (.neg (.classMem (.cv y) C))
        (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z)))))
      (synWa (.neg (.classMem (.cv y) C))
        (synWss (synCdif D C) (synCima R (synCsn (.cv y)))))
      y D p0042
  have p0044 :=
    @gSyl (synWrex x D (.neg (.classMem (.cv x) C)))
      (synWrex y D (synWa (.neg (.classMem (.cv y) C))
          (synWral z D (.imp (.neg (.classMem (.cv z) C)) (synWbr (.cv y) R (.cv z))))))
      (synWrex y D (synWa (.neg (.classMem (.cv y) C))
          (synWss (synCdif D C) (synCima R (synCsn (.cv y))))))
      p0013 p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_weincsegsscutndv`. -/
@[expose]
noncomputable def gWeincsegsscutndv (x : Var) (y : Var) (D : Class) (R : Class)
    (_dv_x_y : x ≠ y) (hyp_weincsegsscutndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (synWss (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
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
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    z ∉
      ((synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
              (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_D, fresh_z_ne_y, fresh_z_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv z) (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))))
  have p0001 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv z) (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))))
  have p0002 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
  have p0003 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0002
      p0003
  have p0005 := @gStrictsegdifinindv x D R
  have p0006 :=
    @gUneq1i (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))
      (synCsn (.cv x)) p0005
  have p0007 :=
    @gA1i
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synCun
          (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))
          (synCsn (.cv x))))
      (.classMem (.cv x) D) p0006
  have p0008 := @gId (.classMem (.cv x) D)
  have p0009 := @gWppweref D R
  have p0010 := Nominal.mp hyp_weincsegsscutndv_1 p0009
  have p0011 := @gA1i (synWbr R (synCref) D) (.classMem (.cv x) D) p0010
  have p0013 := @gRefd (.classMem (.cv x) D) D R (.cv x) p0011 p0008
  have p0014 := @gEliniseg R (.cv x) (.cv x)
  have p0015 :=
    @gSylibr (.classMem (.cv x) D) (synWbr (.cv x) R (.cv x))
      (.classMem (.cv x) (synCima (synCcnv R) (synCsn (.cv x)))) p0013 p0014
  have p0016 :=
    @gJca (.classMem (.cv x) D) (.classMem (.cv x) D)
      (.classMem (.cv x) (synCima (synCcnv R) (synCsn (.cv x)))) p0008 p0015
  have p0017 := @gElin (.cv x) D (synCima (synCcnv R) (synCsn (.cv x)))
  have p0018 :=
    @gSylibr (.classMem (.cv x) D)
      (synWa (.classMem (.cv x) D)
        (.classMem (.cv x) (synCima (synCcnv R) (synCsn (.cv x)))))
      (.classMem (.cv x) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))) p0016
      p0017
  have p0019 :=
    @gNnsucelrlem4 (.cv x) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
  have p0020 :=
    @gSyl (.classMem (.cv x) D)
      (.classMem (.cv x) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (.classEq (synCun (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x))))
            (synCsn (.cv x))) (synCsn (.cv x)))
        (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      p0018 p0019
  have p0021 :=
    @gEqtrd (.classMem (.cv x) D)
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      (synCun
        (synCdif (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (synCsn (.cv x)))
        (synCsn (.cv x)))
      (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) p0007 p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv x) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      p0004 p0021
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      p0001 p0022
  have p0024 :=
    @gEleqtrd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (.cv z)
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) p0000 p0023
  have p0025 := @gElin (.cv z) D (synCima (synCcnv R) (synCsn (.cv x)))
  have p0026 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (.classMem (.cv z) (synCin D (synCima (synCcnv R) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x)))))
      p0024 p0025
  have p0027 :=
    @gSimpl (.classMem (.cv z) D)
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x)))))
      (.classMem (.cv z) D) p0026 p0027
  have p0029 := @gWppwepo D R
  have p0030 := Nominal.mp hyp_weincsegsscutndv_1 p0029
  have p0031 := @gPorta D R
  have p0032 :=
    @gSimp2bi (synWbr R (synCpartial) D) (synWbr R (synCref) D)
      (synWbr R (synCtrans) D) (synWbr R (synCantisym) D) p0031
  have p0033 := Nominal.mp p0030 p0032
  have p0034 :=
    @gA1i (synWbr R (synCtrans) D)
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0033
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv x) D) p0001 p0004
  have p0071 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0072 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0002
      p0071
  have p0073 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv y) D) p0001 p0072
  have p0101 :=
    @gSimpr (.classMem (.cv z) D)
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
  have p0102 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x)))))
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x)))) p0026 p0101
  have p0103 := @gEliniseg R (.cv x) (.cv z)
  have p0104 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (.classMem (.cv z) (synCima (synCcnv R) (synCsn (.cv x))))
      (synWbr (.cv z) R (.cv x)) p0102 p0103
  have p0106 := @gWppweconnex D R
  have p0107 := Nominal.mp hyp_weincsegsscutndv_1 p0106
  have p0108 :=
    @gA1i (synWbr R (synCconnex) D)
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      p0107
  have p0115 :=
    @gConnexd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      D R (.cv x) (.cv y) p0108 p0004 p0072
  have p0116 := @gId (synWbr (.cv x) R (.cv y))
  have p0117 :=
    @gA1i (.imp (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R (.cv y)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      p0116
  have p0118 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
  have p0140 :=
    @gNeleqtrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      (synCin D (synCima (synCcnv R) (synCsn (.cv x)))) (.cv y) p0118 p0022
  have p0141 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x))
  have p0145 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (synWbr (.cv y) R (.cv x)))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv y) D) p0141 p0072
  have p0146 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x))
  have p0147 := @gEliniseg R (.cv x) (.cv y)
  have p0148 :=
    @gSylibr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x)))) p0146 p0147
  have p0149 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (synWbr (.cv y) R (.cv x)))
      (.classMem (.cv y) D) (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x))))
      p0145 p0148
  have p0150 := @gElin (.cv y) D (synCima (synCcnv R) (synCsn (.cv x)))
  have p0151 :=
    @gSylibr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classMem (.cv y) D)
        (.classMem (.cv y) (synCima (synCcnv R) (synCsn (.cv x)))))
      (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))) p0149
      p0150
  have p0152 :=
    @gEx
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))) p0151
  have p0153 :=
    @gCon3d
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x))
      (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))) p0152
  have p0154 :=
    @gMpd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) (synCin D (synCima (synCcnv R) (synCsn (.cv x))))))
      (.neg (synWbr (.cv y) R (.cv x))) p0140 p0153
  have p0155 :=
    @gPm221d
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x)) (synWbr (.cv x) R (.cv y)) p0154
  have p0156 :=
    @gJaod
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x))
      p0117 p0155
  have p0157 :=
    @gMpd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWo (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv x)))
      (synWbr (.cv x) R (.cv y)) p0115 p0156
  have p0158 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWbr (.cv x) R (.cv y)) p0001 p0157
  have p0159 :=
    @gTrd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      D R (.cv z) (.cv x) (.cv y) p0034 p0028 p0068 p0073 p0104 p0158
  have p0163 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0001 p0118
  have p0164 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (.classMem (.cv z) (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))))
      (.neg (.classMem (.cv y) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      p0000 p0163
  have p0165 :=
    @gNelne2 (.cv z) (.cv y)
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
  have p0166 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))) (.neg (.classMem (.cv y) (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (synWne (.cv z) (.cv y)) p0164 p0165
  have p0167 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWbr (.cv z) R (.cv y)) (synWne (.cv z) (.cv y)) p0159 p0166
  have p0168 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv y)) (synWne (.cv z) (.cv y)))
      p0028 p0167
  have p0169 := @gElstrictseg y z D R
  have p0170 :=
    @gSylibr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg
            (.classMem (.cv y) (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCsn (.cv x)))))) (.classMem (.cv z) (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv y)) (synWne (.cv z) (.cv y))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0168 p0169
  have p0171 :=
    @gEx
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      (.classMem (.cv z) (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCsn (.cv x))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0170
  have p0172 :=
    @gSsrdv
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.neg (.classMem (.cv y)
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCsn (.cv x))))))
      z
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCsn (.cv x)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0171
  exact p0172


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wedownexactcutndv`. -/
@[expose]
noncomputable def gWedownexactcutndv (x : Var) (C : Class) (D : Class) (R : Class)
    (hyp_wedownexactcutndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classEq C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
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
  have dv_cache_0001 :
    y ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gId
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
  have p0001 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (synWss (synCdif D C) (synCima R (synCsn (.cv x)))))
      (synWss C (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0002 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWss C (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0000 p0001
  have p0003 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0004 := @gElstrictseg x y D R
  have p0005 :=
    @gSylib
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      p0003 p0004
  have p0006 :=
    @gSimprr (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (synWne (.cv y) (.cv x)) p0005 p0006
  have p0008 := @gWppweantisym D R
  have p0009 := Nominal.mp hyp_wedownexactcutndv_1 p0008
  have p0010 :=
    @gA1i (synWbr R (synCantisym) D)
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) C))
  have p0015 :=
    @gSimpl (.classMem (.cv y) D)
      (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x)))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (.classMem (.cv y) D) p0005 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y) D) p0011 p0016
  have p0019 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0020 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (synWss (synCdif D C) (synCima R (synCsn (.cv x)))))
      (synWss C (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (synWss (synCdif D C) (synCima R (synCsn (.cv x)))))
      p0019 p0020
  have p0022 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
      (synWss (synCdif D C) (synCima R (synCsn (.cv x))))
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (synWss (synCdif D C) (synCima R (synCsn (.cv x)))))
      (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) p0021 p0022
  have p0024 := @gSimpl (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C))) (.classMem (.cv x) D)
      p0023 p0024
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv x) D) p0011 p0025
  have p0031 :=
    @gSimprl (.classMem (.cv y) D) (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classMem (.cv y) D)
        (synWa (synWbr (.cv y) R (.cv x)) (synWne (.cv y) (.cv x))))
      (synWbr (.cv y) R (.cv x)) p0005 p0031
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWbr (.cv y) R (.cv x)) p0011 p0032
  have p0038 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
      (synWss (synCdif D C) (synCima R (synCsn (.cv x))))
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
        (synWss (synCdif D C) (synCima R (synCsn (.cv x)))))
      (synWss (synCdif D C) (synCima R (synCsn (.cv x)))) p0021 p0038
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWss (synCdif D C) (synCima R (synCsn (.cv x)))) p0011 p0039
  have p0048 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) C))
  have p0049 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (.classMem (.cv y) D) (.neg (.classMem (.cv y) C)) p0017 p0048
  have p0050 := @gEldif (.cv y) D C
  have p0051 :=
    @gSylibr
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (synWa (.classMem (.cv y) D) (.neg (.classMem (.cv y) C)))
      (.classMem (.cv y) (synCdif D C)) p0049 p0050
  have p0052 :=
    @gSseldd
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (synCdif D C) (synCima R (synCsn (.cv x))) (.cv y) p0040 p0051
  have p0053 := @gElimasn R (.cv x) (.cv y)
  have p0054 := (Nominal.biimpRefl (synWbr (.cv x) R (.cv y)))
  have p0055 :=
    @gBitr4i (.classMem (.cv y) (synCima R (synCsn (.cv x))))
      (.classMem (synCop (.cv x) (.cv y)) R) (synWbr (.cv x) R (.cv y)) p0053 p0054
  have p0056 :=
    @gSylib
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      (.classMem (.cv y) (synCima R (synCsn (.cv x)))) (synWbr (.cv x) R (.cv y)) p0052
      p0055
  have p0057 :=
    @gAntid
      (synWa (synWa (synWa
            (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
              (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classMem (.cv y) C)))
      D R (.cv y) (.cv x) p0010 p0017 p0026 p0033 p0056
  have p0058 :=
    @gEx
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) C)) (.classEq (.cv y) (.cv x)) p0057
  have p0059 :=
    @gNecon3ad
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classMem (.cv y) C)) (.cv y) (.cv x) p0058
  have p0060 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWne (.cv y) (.cv x)) (.neg (.neg (.classMem (.cv y) C))) p0007 p0059
  have p0061 :=
    @gNotnotrd
      (synWa (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
            (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y) C) p0060
  have p0062 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv y) C) p0061
  have p0063 :=
    @gSsrdv
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      y (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) C
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0062
  have p0064 :=
    @gEqssd
      (synWa (synWa (synWa (.classMem (.cv x) D) (.neg (.classMem (.cv x) C)))
          (synWss (synCdif D C) (synCima R (synCsn (.cv x))))) (synWss C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      C (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0002
      p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end
