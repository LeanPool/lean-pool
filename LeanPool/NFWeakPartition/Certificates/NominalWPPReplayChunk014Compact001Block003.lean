/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdprj1valV`. -/
@[expose]
noncomputable def gFdprj1valV (x : Var) (C : Class) (D : Class)
    (_dv_C_D : Disjoint C.fv D.fv) (_dv_C_x : x ∉ C.fv) (_dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
        (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
          (.classEq (.cv x) (synCsn (synCsn D))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ C.fv ∪ D.fv
  let a : Var := freshVar proofSupport 0
  let c : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_c_ne_b : c ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have dv_cache_0001 : a ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_a_not_C, fresh_a_not_D, or_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_b_not_C, fresh_b_not_D, or_false, not_false_eq_true])
  have dv_cache_0006 : c ∉ ((synCopk C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_c_not_C, fresh_c_not_D, or_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((synCidk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((synCidk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : c ∉ ((synCidk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0012 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0013 :
    a ∉ ((synWa (.classMem C (synCvv)) (.classMem D (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_a_not_C, fresh_a_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    b ∉ ((synWa (.classMem C (synCvv)) (.classMem D (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_b_not_C, fresh_b_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    c ∉ ((synWa (.classMem C (synCvv)) (.classMem D (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_c_not_C, fresh_c_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : b ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_C, not_false_eq_true])
  have dv_cache_0017 :
    b ∉
      ((synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_ne_c, fresh_b_not_D,
          or_false, not_false_eq_true])
  have dv_cache_0018 : c ∉ (D).fv :=
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
        simp only [fresh_c_not_D, not_false_eq_true])
  have dv_cache_0019 :
    c ∉
      ((synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a, fresh_c_not_D, or_false,
          not_false_eq_true])
  have dv_cache_0020 : a ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_D, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((Wff.classEq (.cv x) (synCsn (synCsn D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_D, or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCfdprj1))
  have p0001 :=
    @gEleq2i (synCfdprj1) (synCins2k (synCidk)) (synCopk (.cv x) (synCopk C D))
      p0000
  have p0002 := @gVex x
  have p0003 := @gOpkex C D
  have p0004 :=
    @gOpkelins2kg a b c (.cv x) (synCopk C D) (synCidk) (synCvv) (synCvv)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0005 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem (synCopk C D) (synCvv))
      (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCins2k (synCidk))) (synWex a
          (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
                (.classMem (synCopk (.cv a) (.cv c)) (synCidk)))))))
      p0002 p0003 p0004
  have p0006 :=
    @gBitri (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCins2k (synCidk)))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
              (.classMem (synCopk (.cv a) (.cv c)) (synCidk))))))
      p0001 p0005
  have p0007 :=
    @gA1i
      (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1)) (synWex a (synWex b
            (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
                (.classMem (synCopk (.cv a) (.cv c)) (synCidk)))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0006
  have p0008 := @gBiid (.classEq (.cv x) (synCsn (synCsn (.cv a))))
  have p0009 :=
    @gA1i
      (synWb (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (.classEq (.cv x) (synCsn (synCsn (.cv a)))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0008
  have p0010 := @gVex c
  have p0011 := @gOpkthg C D (.cv b) (.cv c) (synCvv) (synCvv) (synCvv)
  have p0012 :=
    @gMp3an3 (.classMem C (synCvv)) (.classMem D (synCvv))
      (.classMem (.cv c) (synCvv))
      (synWb (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
        (synWa (.classEq C (.cv b)) (.classEq D (.cv c))))
      p0010 p0011
  have p0013 := @gEqcom C (.cv b)
  have p0014 := @gEqcom D (.cv c)
  have p0015 :=
    @gAnbi12i (.classEq C (.cv b)) (.classEq (.cv b) C) (.classEq D (.cv c))
      (.classEq (.cv c) D) p0013 p0014
  have p0016 :=
    @gA1i
      (synWb (synWa (.classEq C (.cv b)) (.classEq D (.cv c)))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0015
  have p0017 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
      (synWa (.classEq C (.cv b)) (.classEq D (.cv c)))
      (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) p0012 p0016
  have p0018 := @gVex a
  have p0020 := @gOpkelidkg (.cv a) (.cv c) (synCvv) (synCvv)
  have p0021 :=
    @gMp2an (.classMem (.cv a) (synCvv)) (.classMem (.cv c) (synCvv))
      (synWb (.classMem (synCopk (.cv a) (.cv c)) (synCidk)) (.classEq (.cv a) (.cv c)))
      p0018 p0010 p0020
  have p0022 :=
    @gA1i
      (synWb (.classMem (synCopk (.cv a) (.cv c)) (synCidk)) (.classEq (.cv a) (.cv c)))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0021
  have p0023 :=
    @gN3anbi123d (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
      (synWa (.classEq (.cv b) C) (.classEq (.cv c) D))
      (.classMem (synCopk (.cv a) (.cv c)) (synCidk)) (.classEq (.cv a) (.cv c)) p0009
      p0017 p0022
  have p0024 :=
    @gN3exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
        (.classMem (synCopk (.cv a) (.cv c)) (synCidk)))
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0023
  have p0025 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (synCopk C D) (synCopk (.cv b) (.cv c)))
              (.classMem (synCopk (.cv a) (.cv c)) (synCidk))))))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))))))
      p0007 p0024
  have p0026 :=
    @gN3anass (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))
  have p0027 :=
    @gAnass (.classEq (.cv b) C) (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))
  have p0028 :=
    @gAnbi2i
      (synWa (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      (.classEq (.cv x) (synCsn (synCsn (.cv a)))) p0027
  have p0029 :=
    @gBitri
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      p0026 p0028
  have p0030 :=
    @gAn12 (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv b) C)
      (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))
  have p0031 :=
    @gBitri
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      p0029 p0030
  have p0032 :=
    @gA1i
      (synWb (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
        (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0031
  have p0033 :=
    @gN3exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c)))
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      a b c dv_cache_0013 dv_cache_0014 dv_cache_0015 p0032
  have p0034 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWex b (synWex c (synW3a (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv b) C) (.classEq (.cv c) D)) (.classEq (.cv a) (.cv c))))))
      (synWex a (synWex b (synWex c (synWa (.classEq (.cv b) C)
              (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      p0025 p0033
  have p0035 :=
    @gExcom
      (synWa (.classEq (.cv b) C) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      b c
  have p0036 :=
    @gExbii
      (synWex b (synWex c (synWa (.classEq (.cv b) C)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))
      (synWex c (synWex b (synWa (.classEq (.cv b) C)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))
      a p0035
  have p0037 :=
    @gA1i
      (synWb (synWex a (synWex b (synWex c (synWa (.classEq (.cv b) C)
                (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                  (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))) (synWex a
          (synWex c (synWex b (synWa (.classEq (.cv b) C)
                (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                  (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0036
  have p0038 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWex b (synWex c (synWa (.classEq (.cv b) C)
              (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      (synWex a (synWex c (synWex b (synWa (.classEq (.cv b) C)
              (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      p0034 p0037
  have p0039 := @gSimpl (.classMem C (synCvv)) (.classMem D (synCvv))
  have p0040 :=
    @gBiidd (.classEq (.cv b) C)
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
  have p0041 :=
    @gCeqsexgv
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      b C (synCvv) dv_cache_0016 dv_cache_0017 p0040
  have p0042 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem C (synCvv))
      (synWb (synWex b (synWa (.classEq (.cv b) C)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
        (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))))
      p0039 p0041
  have p0043 :=
    @gN2exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWex b (synWa (.classEq (.cv b) C)
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      a c dv_cache_0013 dv_cache_0015 p0042
  have p0044 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWex c (synWex b (synWa (.classEq (.cv b) C)
              (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
                (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))))
      (synWex a (synWex c (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      p0038 p0043
  have p0045 :=
    @gAn12 (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv c) D)
      (.classEq (.cv a) (.cv c))
  have p0046 :=
    @gA1i
      (synWb (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)))) (synWa (.classEq (.cv c) D)
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv c)))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0045
  have p0047 :=
    @gN2exbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
        (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))
      (synWa (.classEq (.cv c) D) (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
          (.classEq (.cv a) (.cv c))))
      a c dv_cache_0013 dv_cache_0015 p0046
  have p0048 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWex c (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
            (synWa (.classEq (.cv c) D) (.classEq (.cv a) (.cv c))))))
      (synWex a (synWex c (synWa (.classEq (.cv c) D)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (.cv a) (.cv c))))))
      p0044 p0047
  have p0049 := @gSimpr (.classMem C (synCvv)) (.classMem D (synCvv))
  have p0050 := @gEqeq2 (.cv c) D (.cv a)
  have p0051 :=
    @gAnbi2d (.classEq (.cv c) D) (.classEq (.cv a) (.cv c)) (.classEq (.cv a) D)
      (.classEq (.cv x) (synCsn (synCsn (.cv a)))) p0050
  have p0052 :=
    @gCeqsexgv
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv c)))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)) c D
      (synCvv) dv_cache_0018 dv_cache_0019 p0051
  have p0053 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem D (synCvv))
      (synWb (synWex c (synWa (.classEq (.cv c) D)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv c)))))
        (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)))
      p0049 p0052
  have p0054 :=
    @gExbidv (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWex c (synWa (.classEq (.cv c) D)
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) (.cv c)))))
      (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)) a
      dv_cache_0013 p0053
  have p0055 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWex c (synWa (.classEq (.cv c) D)
            (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a))))
              (.classEq (.cv a) (.cv c))))))
      (synWex a (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)))
      p0048 p0054
  have p0056 :=
    @gAncom (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)
  have p0057 :=
    @gExbii (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D))
      (synWa (.classEq (.cv a) D) (.classEq (.cv x) (synCsn (synCsn (.cv a))))) a p0056
  have p0058 :=
    @gA1i
      (synWb (synWex a
          (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)))
        (synWex a
          (synWa (.classEq (.cv a) D) (.classEq (.cv x) (synCsn (synCsn (.cv a)))))))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv))) p0057
  have p0059 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWa (.classEq (.cv x) (synCsn (synCsn (.cv a)))) (.classEq (.cv a) D)))
      (synWex a (synWa (.classEq (.cv a) D) (.classEq (.cv x) (synCsn (synCsn (.cv a))))))
      p0055 p0058
  have p0061 := @gSneq (.cv a) D
  have p0062 := @gSneqd (.classEq (.cv a) D) (synCsn (.cv a)) (synCsn D) p0061
  have p0063 :=
    @gEqeq2d (.classEq (.cv a) D) (synCsn (synCsn (.cv a))) (synCsn (synCsn D))
      (.cv x) p0062
  have p0064 :=
    @gCeqsexgv (.classEq (.cv x) (synCsn (synCsn (.cv a))))
      (.classEq (.cv x) (synCsn (synCsn D))) a D (synCvv) dv_cache_0020 dv_cache_0021
      p0063
  have p0065 :=
    @gSyl (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem D (synCvv))
      (synWb (synWex a
          (synWa (.classEq (.cv a) D) (.classEq (.cv x) (synCsn (synCsn (.cv a))))))
        (.classEq (.cv x) (synCsn (synCsn D))))
      p0049 p0064
  have p0066 :=
    @gBitrd (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (synWex a (synWa (.classEq (.cv a) D) (.classEq (.cv x) (synCsn (synCsn (.cv a))))))
      (.classEq (.cv x) (synCsn (synCsn D))) p0059 p0065
  exact p0066

/-- Checked nominal proof certificate identified upstream as `g_fde1valJp`. -/
@[expose]
noncomputable def gFde1valJp (A : Class) (B : Class) (C : Class) (D : Class) (e : Var)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_D : Disjoint A.fv D.fv) (_dv_A_e : e ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_D : Disjoint B.fv D.fv) (_dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (_dv_C_e : e ∉ C.fv) (_dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem C B) (.classMem D B))
        (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))
          (synWa (.classMem (.cv e) A) (.classMem D (.cv e))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({ e } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_e : x ≠ e := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : x ∉ ((synCsn (.cv e))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_e,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCopk C D)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCfdprj1)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdprj1,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCfdmem)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
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
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synWa (.classMem C B) (.classMem D B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_x_not_C,
          fresh_x_not_B, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCsn (synCsn D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_D,
          not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_e, fresh_x_not_D, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCfde1 A B))
  have p0001 :=
    @gEleq2i (synCfde1 A B)
      (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B))))
      (synWa (.classMem C B) (.classMem D B)) p0001
  have p0003 :=
    @gElin (synCopk (synCsn (.cv e)) (synCopk C D))
      (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B)
  have p0004 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B))) (synWa
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
            (synCcomk (synCfdprj1) (synCfdmem)))
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))))
      (synWa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B)))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCcomk (synCfdprj1) (synCfdmem)))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B)))
      p0002 p0004
  have p0006 := @gSnex (.cv e)
  have p0007 := @gOpkex C D
  have p0008 :=
    @gOpkelcok x (synCsn (.cv e)) (synCopk C D) (synCfdprj1) (synCfdmem)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCcomk (synCfdprj1) (synCfdmem))) (synWex x
          (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1)))))
      (synWa (.classMem C B) (.classMem D B)) p0008
  have p0010 := @gBiid (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
  have p0011 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem)))
      (synWa (.classMem C B) (.classMem D B)) p0010
  have p0012 := @gSimpl (.classMem C B) (.classMem D B)
  have p0013 := @gElex C B
  have p0014 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem C B)
      (.classMem C (synCvv)) p0012 p0013
  have p0015 := @gSimpr (.classMem C B) (.classMem D B)
  have p0016 := @gElex D B
  have p0017 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem D B)
      (.classMem D (synCvv)) p0015 p0016
  have p0018 :=
    @gJca (synWa (.classMem C B) (.classMem D B)) (.classMem C (synCvv))
      (.classMem D (synCvv)) p0014 p0017
  have p0019 := @gFdprj1valV x C D dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0020 :=
    @gSyl (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWb (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
        (.classEq (.cv x) (synCsn (synCsn D))))
      p0018 p0019
  have p0021 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))
      (.classEq (.cv x) (synCsn (synCsn D))) p0011 p0020
  have p0022 :=
    @gExbidv (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1)))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classEq (.cv x) (synCsn (synCsn D))))
      x dv_cache_0008 p0021
  have p0023 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj1) (synCfdmem)))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdprj1))))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classEq (.cv x) (synCsn (synCsn D)))))
      p0009 p0022
  have p0024 :=
    @gAncom (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classEq (.cv x) (synCsn (synCsn D)))
  have p0025 :=
    @gA1i
      (synWb (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classEq (.cv x) (synCsn (synCsn D))))
        (synWa (.classEq (.cv x) (synCsn (synCsn D)))
          (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
      (synWa (.classMem C B) (.classMem D B)) p0024
  have p0026 :=
    @gExbidv (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
        (.classEq (.cv x) (synCsn (synCsn D))))
      (synWa (.classEq (.cv x) (synCsn (synCsn D)))
        (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem)))
      x dv_cache_0008 p0025
  have p0027 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj1) (synCfdmem)))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
          (.classEq (.cv x) (synCsn (synCsn D)))))
      (synWex x (synWa (.classEq (.cv x) (synCsn (synCsn D)))
          (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
      p0023 p0026
  have p0028 := @gSnex (synCsn D)
  have p0029 := @gOpkeq2 (.cv x) (synCsn (synCsn D)) (synCsn (.cv e))
  have p0030 :=
    @gEleq1d (.classEq (.cv x) (synCsn (synCsn D)))
      (synCopk (synCsn (.cv e)) (.cv x))
      (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem) p0029
  have p0031 :=
    @gCeqsexgv (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem)) x
      (synCsn (synCsn D)) (synCvv) dv_cache_0009 dv_cache_0010 p0030
  have p0032 := Nominal.mp p0028 p0031
  have p0033 :=
    @gA1i
      (synWb (synWex x (synWa (.classEq (.cv x) (synCsn (synCsn D)))
            (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
        (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem)))
      (synWa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj1) (synCfdmem)))
      (synWex x (synWa (.classEq (.cv x) (synCsn (synCsn D)))
          (.classMem (synCopk (synCsn (.cv e)) (.cv x)) (synCfdmem))))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem)) p0027
      p0033
  have p0036 := @gFdmemvalC B D e
  have p0037 :=
    @gSyl (synWa (.classMem C B) (.classMem D B)) (.classMem D B)
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem))
        (.classMem D (.cv e)))
      p0015 p0036
  have p0038 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj1) (synCfdmem)))
      (.classMem (synCopk (synCsn (.cv e)) (synCsn (synCsn D))) (synCfdmem))
      (.classMem D (.cv e)) p0034 p0037
  have p0039 := (Nominal.classEqRefl (synCfddom A B))
  have p0040 :=
    @gEleq2i (synCfddom A B) (synCxpk (synCpw1 A) (synCxpk B B))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0039
  have p0041 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCxpk (synCpw1 A) (synCxpk B B))))
      (synWa (.classMem C B) (.classMem D B)) p0040
  have p0044 :=
    @gOpkelxpk (synCsn (.cv e)) (synCopk C D) (synCpw1 A) (synCxpk B B) p0006 p0007
  have p0045 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCxpk (synCpw1 A) (synCxpk B B)))
        (synWa (.classMem (synCsn (.cv e)) (synCpw1 A))
          (.classMem (synCopk C D) (synCxpk B B))))
      (synWa (.classMem C B) (.classMem D B)) p0044
  have p0046 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCxpk (synCpw1 A) (synCxpk B B)))
      (synWa (.classMem (synCsn (.cv e)) (synCpw1 A))
        (.classMem (synCopk C D) (synCxpk B B)))
      p0041 p0045
  have p0047 := @gSnelpw1 (.cv e) A
  have p0048 :=
    @gA1i (synWb (.classMem (synCsn (.cv e)) (synCpw1 A)) (.classMem (.cv e) A))
      (synWa (.classMem C B) (.classMem D B)) p0047
  have p0056 := @gOpkelxpkg C D B B (synCvv) (synCvv)
  have p0057 :=
    @gSyl (synWa (.classMem C B) (.classMem D B))
      (synWa (.classMem C (synCvv)) (.classMem D (synCvv)))
      (synWb (.classMem (synCopk C D) (synCxpk B B))
        (synWa (.classMem C B) (.classMem D B)))
      p0018 p0056
  have p0058 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCsn (.cv e)) (synCpw1 A)) (.classMem (.cv e) A)
      (.classMem (synCopk C D) (synCxpk B B)) (synWa (.classMem C B) (.classMem D B))
      p0048 p0057
  have p0059 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (synWa (.classMem (synCsn (.cv e)) (synCpw1 A))
        (.classMem (synCopk C D) (synCxpk B B)))
      (synWa (.classMem (.cv e) A) (synWa (.classMem C B) (.classMem D B))) p0046 p0058
  have p0060 := @gIba (synWa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
  have p0061 :=
    @gBicomd (synWa (.classMem C B) (.classMem D B)) (.classMem (.cv e) A)
      (synWa (.classMem (.cv e) A) (synWa (.classMem C B) (.classMem D B))) p0060
  have p0062 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (synWa (.classMem (.cv e) A) (synWa (.classMem C B) (.classMem D B)))
      (.classMem (.cv e) A) p0059 p0061
  have p0063 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdprj1) (synCfdmem)))
      (.classMem D (.cv e))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B))
      (.classMem (.cv e) A) p0038 p0062
  have p0064 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
          (synCcomk (synCfdprj1) (synCfdmem)))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfddom A B)))
      (synWa (.classMem D (.cv e)) (.classMem (.cv e) A)) p0005 p0063
  have p0065 := @gAncom (.classMem D (.cv e)) (.classMem (.cv e) A)
  have p0066 :=
    @gA1i
      (synWb (synWa (.classMem D (.cv e)) (.classMem (.cv e) A))
        (synWa (.classMem (.cv e) A) (.classMem D (.cv e))))
      (synWa (.classMem C B) (.classMem D B)) p0065
  have p0067 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))
      (synWa (.classMem D (.cv e)) (.classMem (.cv e) A))
      (synWa (.classMem (.cv e) A) (.classMem D (.cv e))) p0064 p0066
  exact p0067

/-- Checked nominal proof certificate identified upstream as `g_sep2valJp`. -/
@[expose]
noncomputable def gSep2valJp (C : Class) (D : Class) (e : Var)
    (dv_C_D : Disjoint C.fv D.fv) (_dv_C_e : e ∉ C.fv) (_dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (synWb (.classMem (.cv e) (synCsep2 C D))
        (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({ e } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_e : z ≠ e := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : Disjoint (C).fv (D).fv := by
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0002 : z ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0003 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_e, not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_singleton,
          fresh_z_not_C, fresh_z_ne_e, fresh_z_not_D, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSep2 z C D
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEleq2i (synCsep2 C D)
      (.cab z (synWo (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
          (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))))
      (.cv e) p0000
  have p0002 := @gVex e
  have p0003 := @gEleq2 (.cv z) (.cv e) C
  have p0004 := @gEleq2 (.cv z) (.cv e) D
  have p0005 :=
    @gNotbid (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e)) p0004
  have p0006 :=
    @gAnbi12d (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e))
      (.neg (.classMem D (.cv z))) (.neg (.classMem D (.cv e))) p0003 p0005
  have p0009 :=
    @gNotbid (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e)) p0003
  have p0010 :=
    @gAnbi12d (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e))
      (.neg (.classMem C (.cv z))) (.neg (.classMem C (.cv e))) p0004 p0009
  have p0011 :=
    @gOrbi12d (.classEq (.cv z) (.cv e))
      (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
      (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
      (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))
      (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))) p0006 p0010
  have p0012 :=
    @gElab
      (synWo (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
        (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      z (.cv e) dv_cache_0004 dv_cache_0005 p0002 p0011
  have p0013 :=
    @gBitri (.classMem (.cv e) (synCsep2 C D))
      (.classMem (.cv e) (.cab z
          (synWo (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
            (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))))
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      p0001 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdsepvalJ`. -/
@[expose]
noncomputable def gFdsepvalJ (A : Class) (B : Class) (C : Class) (D : Class) (e : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_D : Disjoint A.fv D.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_D : Disjoint B.fv D.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv)
    (dv_C_e : e ∉ C.fv) (dv_D_e : e ∉ D.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem C B) (.classMem D B))
        (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B))
          (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({ e } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_e : z ≠ e := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : e ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_e, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : e ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_e, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : e ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_e, not_false_eq_true])
  have dv_cache_0010 : e ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_e, not_false_eq_true])
  have dv_cache_0011 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0012 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv e)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_e, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_singleton,
          fresh_z_not_C, fresh_z_ne_e, fresh_z_not_D, or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCfdsep A B))
  have p0001 :=
    @gEleq2i (synCfdsep A B) (synCsymdif (synCfde0 A B) (synCfde1 A B))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0000
  have p0002 :=
    @gElsymdif (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B)
      (synCfde1 A B)
  have p0003 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCsymdif (synCfde0 A B) (synCfde1 A B)))
      (.neg (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))))
      p0001 p0002
  have p0004 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B)) (.neg
          (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
            (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B)))))
      (synWa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @gFde0valJp A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0006 :=
    @gFde1valJp A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0007 :=
    @gBibi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
      (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))
      (synWa (.classMem (.cv e) A) (.classMem D (.cv e))) p0005 p0006
  have p0008 :=
    @gNotbid (synWa (.classMem C B) (.classMem D B))
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
        (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B)))
      (synWb (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
        (synWa (.classMem (.cv e) A) (.classMem D (.cv e))))
      p0007
  have p0009 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B))
      (.neg (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde0 A B))
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfde1 A B))))
      (.neg (synWb (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (synWa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      p0004 p0008
  have p0010 := @gXordi (.classMem (.cv e) A) (.classMem C (.cv e)) (.classMem D (.cv e))
  have p0011 :=
    @gBicomi
      (synWa (.classMem (.cv e) A) (.neg (synWb (.classMem C (.cv e)) (.classMem D (.cv e)))))
      (.neg (synWb (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (synWa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      p0010
  have p0012 := @gXor (.classMem C (.cv e)) (.classMem D (.cv e))
  have p0013 :=
    @gAnbi2i (.neg (synWb (.classMem C (.cv e)) (.classMem D (.cv e))))
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      (.classMem (.cv e) A) p0012
  have p0014 :=
    @gBitri
      (.neg (synWb (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (synWa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      (synWa (.classMem (.cv e) A) (.neg (synWb (.classMem C (.cv e)) (.classMem D (.cv e)))))
      (synWa (.classMem (.cv e) A)
        (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
      p0011 p0013
  have p0015 :=
    @gA1i
      (synWb (.neg (synWb (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
            (synWa (.classMem (.cv e) A) (.classMem D (.cv e))))) (synWa (.classMem (.cv e) A)
          (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
            (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))))
      (synWa (.classMem C B) (.classMem D B)) p0014
  have p0016 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B))
      (.neg (synWb (synWa (.classMem (.cv e) A) (.classMem C (.cv e)))
          (synWa (.classMem (.cv e) A) (.classMem D (.cv e)))))
      (synWa (.classMem (.cv e) A)
        (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
      p0009 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSep2 z C D
      dv_cache_0008 dv_cache_0011 dv_cache_0012
  have p0018 :=
    @gEleq2i (synCsep2 C D)
      (.cab z (synWo (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
          (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))))
      (.cv e) p0017
  have p0019 := @gVex e
  have p0020 := @gEleq2 (.cv z) (.cv e) C
  have p0021 := @gEleq2 (.cv z) (.cv e) D
  have p0022 :=
    @gNotbid (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e)) p0021
  have p0023 :=
    @gAnbi12d (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e))
      (.neg (.classMem D (.cv z))) (.neg (.classMem D (.cv e))) p0020 p0022
  have p0026 :=
    @gNotbid (.classEq (.cv z) (.cv e)) (.classMem C (.cv z)) (.classMem C (.cv e)) p0020
  have p0027 :=
    @gAnbi12d (.classEq (.cv z) (.cv e)) (.classMem D (.cv z)) (.classMem D (.cv e))
      (.neg (.classMem C (.cv z))) (.neg (.classMem C (.cv e))) p0021 p0026
  have p0028 :=
    @gOrbi12d (.classEq (.cv z) (.cv e))
      (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
      (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
      (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z))))
      (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))) p0023 p0027
  have p0029 :=
    @gElab
      (synWo (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
        (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      z (.cv e) dv_cache_0013 dv_cache_0014 p0019 p0028
  have p0030 :=
    @gBitri (.classMem (.cv e) (synCsep2 C D))
      (.classMem (.cv e) (.cab z
          (synWo (synWa (.classMem C (.cv z)) (.neg (.classMem D (.cv z))))
            (synWa (.classMem D (.cv z)) (.neg (.classMem C (.cv z)))))))
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      p0018 p0029
  have p0031 :=
    @gBicomi (.classMem (.cv e) (synCsep2 C D))
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      p0030
  have p0032 :=
    @gAnbi2i
      (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
        (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e)))))
      (.classMem (.cv e) (synCsep2 C D)) (.classMem (.cv e) A) p0031
  have p0033 :=
    @gA1i
      (synWb (synWa (.classMem (.cv e) A)
          (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
            (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
        (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))))
      (synWa (.classMem C B) (.classMem D B)) p0032
  have p0034 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B))
      (synWa (.classMem (.cv e) A)
        (synWo (synWa (.classMem C (.cv e)) (.neg (.classMem D (.cv e))))
          (synWa (.classMem D (.cv e)) (.neg (.classMem C (.cv e))))))
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) p0016 p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_strictbr`. -/
@[expose]
noncomputable def gStrictbr (R : Class) (e : Var) (c : Var) :
    Nominal.NPrf
      (synWb (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e)))) :=
  by
  have p0000 := @gBrdif (.cv c) (.cv e) R (synCid)
  have p0001 := @gVex e
  have p0002 := @gIdeq (.cv c) (.cv e) p0001
  have p0003 :=
    @gNotbii (synWbr (.cv c) (synCid) (.cv e)) (.classEq (.cv c) (.cv e)) p0002
  have p0004 := (Nominal.biimpRefl (synWne (.cv c) (.cv e)))
  have p0005 :=
    @gBicomi (synWne (.cv c) (.cv e)) (.neg (.classEq (.cv c) (.cv e))) p0004
  have p0006 :=
    @gBitri (.neg (synWbr (.cv c) (synCid) (.cv e))) (.neg (.classEq (.cv c) (.cv e)))
      (synWne (.cv c) (.cv e)) p0003 p0005
  have p0007 :=
    @gAnbi2i (.neg (synWbr (.cv c) (synCid) (.cv e))) (synWne (.cv c) (.cv e))
      (synWbr (.cv c) R (.cv e)) p0006
  have p0008 :=
    @gBitri (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (synWa (synWbr (.cv c) R (.cv e)) (.neg (synWbr (.cv c) (synCid) (.cv e))))
      (synWa (synWbr (.cv c) R (.cv e)) (synWne (.cv c) (.cv e))) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fdnonminval0J`. -/
@[expose]
noncomputable def gFdnonminval0J (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv)
    (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv)
    (_dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (_dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (_dv_B_e : e ∉ B.fv)
    (dv_C_D : Disjoint C.fv D.fv) (_dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv)
    (_dv_C_e : e ∉ C.fv) (_dv_D_R : Disjoint D.fv R.fv) (dv_D_c : c ∉ D.fv)
    (_dv_D_e : e ∉ D.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (synWa (.classMem C B) (.classMem D B)) (synWb
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
          (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
              (.classMem (.cv c) (synCsep2 C D)))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({ e } : Finset Var) ∪ ({ c } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_e : x ≠ e := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_e_ne_x : e ≠ x := Ne.symm fresh_x_ne_e
  have fresh_x_ne_c : x ≠ c := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_c, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : c ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_c, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : c ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_c, not_false_eq_true])
  have dv_cache_0010 : c ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_c, not_false_eq_true])
  have dv_cache_0011 : c ∉ ((synWa (.classMem C B) (.classMem D B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_C_c, dv_B_c,
          dv_D_c, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synCsn (.cv e))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_e,
          not_false_eq_true])
  have dv_cache_0013 : x ∉ ((synCopk C D)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((synCfdsep A B)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCcnvk (synCfdlift (synCdif R (synCid))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdlift,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : c ∉ ((synCdif R (synCid))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, dv_R_c,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : e ∉ ((synCdif R (synCid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, dv_R_e,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((synCdif R (synCid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : c ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show c ≠ e from (by exact dv_c_e))
  have dv_cache_0020 : c ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show c ≠ x from (by exact fresh_c_ne_x))
  have dv_cache_0021 : e ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show e ≠ x from (by exact fresh_e_ne_x))
  have dv_cache_0022 :
    c ∉ ((Wff.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, dv_C_c, dv_D_c, dv_A_c, dv_B_c, or_false,
          not_false_eq_true])
  have dv_cache_0023 : x ∉ ((synCsn (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_c,
          not_false_eq_true])
  have dv_cache_0024 :
    x ∉
      ((synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdsep, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_e, fresh_x_not_R, fresh_x_not_C,
          fresh_x_not_D, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gFdsepvalJ A B C D c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 :=
    @gAnbi2d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B))
      (synWa (.classMem (.cv c) A) (.classMem (.cv c) (synCsep2 C D)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) p0000
  have p0002 :=
    @gAn12 (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) (.classMem (.cv c) A)
      (.classMem (.cv c) (synCsep2 C D))
  have p0003 :=
    @gA1i
      (synWb (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (synWa (.classMem (.cv c) A) (.classMem (.cv c) (synCsep2 C D))))
        (synWa (.classMem (.cv c) A) (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      (synWa (.classMem C B) (.classMem D B)) p0002
  have p0004 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B)))
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (synWa (.classMem (.cv c) A) (.classMem (.cv c) (synCsep2 C D))))
      (synWa (.classMem (.cv c) A) (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (.cv c) (synCsep2 C D))))
      p0001 p0003
  have p0005 :=
    @gExbidv (synWa (.classMem C B) (.classMem D B))
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B)))
      (synWa (.classMem (.cv c) A) (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (.cv c) (synCsep2 C D))))
      c dv_cache_0011 p0004
  have p0006 := (Nominal.classEqRefl (synCfdnonmin R A B))
  have p0007 :=
    @gEleq2i (synCfdnonmin R A B)
      (synCcomk (synCfdsep A B) (synCcnvk (synCfdlift (synCdif R (synCid)))))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0006
  have p0008 := @gSnex (.cv e)
  have p0009 := @gOpkex C D
  have p0010 :=
    @gOpkelcok x (synCsn (.cv e)) (synCopk C D) (synCfdsep A B)
      (synCcnvk (synCfdlift (synCdif R (synCid)))) dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 p0008 p0009
  have p0011 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCcomk (synCfdsep A B) (synCcnvk (synCfdlift (synCdif R (synCid))))))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x))
            (synCcnvk (synCfdlift (synCdif R (synCid)))))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      p0007 p0010
  have p0013 := @gVex x
  have p0014 :=
    @gOpkelcnvk (synCsn (.cv e)) (.cv x) (synCfdlift (synCdif R (synCid))) p0008
      p0013
  have p0015 := @gBiid (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))
  have p0016 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (.cv e)) (.cv x))
        (synCcnvk (synCfdlift (synCdif R (synCid)))))
      (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCfdlift (synCdif R (synCid))))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)) p0014 p0015
  have p0017 :=
    @gExbii
      (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x))
          (synCcnvk (synCfdlift (synCdif R (synCid)))))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      (synWa (.classMem (synCopk (.cv x) (synCsn (.cv e)))
          (synCfdlift (synCdif R (synCid))))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      x p0016
  have p0018 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWex x (synWa (.classMem (synCopk (synCsn (.cv e)) (.cv x))
            (synCcnvk (synCfdlift (synCdif R (synCid)))))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      (synWex x (synWa (.classMem (synCopk (.cv x) (synCsn (.cv e)))
            (synCfdlift (synCdif R (synCid))))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      p0011 p0017
  have p0019 :=
    @gFdliftval1 x (synCdif R (synCid)) e c dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0021 :=
    @gAnbi12i
      (.classMem (synCopk (.cv x) (synCsn (.cv e))) (synCfdlift (synCdif R (synCid))))
      (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c)))
          (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)) p0019 p0015
  have p0022 :=
    @gExbii
      (synWa (.classMem (synCopk (.cv x) (synCsn (.cv e)))
          (synCfdlift (synCdif R (synCid))))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      (synWa (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      x p0021
  have p0023 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWex x (synWa (.classMem (synCopk (.cv x) (synCsn (.cv e)))
            (synCfdlift (synCdif R (synCid))))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      (synWex x (synWa (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c)))
              (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      p0018 p0022
  have p0024 :=
    @gN1941v
      (synWa (.classEq (.cv x) (synCsn (.cv c)))
        (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)) c dv_cache_0022
  have p0025 :=
    @gBicomi
      (synWex c (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      (synWa (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      p0024
  have p0026 :=
    @gExbii
      (synWa (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      (synWex c (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      x p0025
  have p0027 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWex x (synWa (synWex c (synWa (.classEq (.cv x) (synCsn (.cv c)))
              (synWbr (.cv c) (synCdif R (synCid)) (.cv e))))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      (synWex x (synWex c (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
              (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))))
      p0023 p0026
  have p0028 :=
    @gExcom
      (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
          (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      x c
  have p0029 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWex x (synWex c (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
              (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))))
      (synWex c (synWex x (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
              (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))))
      p0027 p0028
  have p0030 :=
    @gAnass (.classEq (.cv x) (synCsn (.cv c)))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))
  have p0031 :=
    @gExbii
      (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
          (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      (synWa (.classEq (.cv x) (synCsn (.cv c)))
        (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      x p0030
  have p0032 :=
    @gExbii
      (synWex x (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
          (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))
      (synWex x (synWa (.classEq (.cv x) (synCsn (.cv c)))
          (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))))
      c p0031
  have p0033 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWex c (synWex x (synWa (synWa (.classEq (.cv x) (synCsn (.cv c)))
              (synWbr (.cv c) (synCdif R (synCid)) (.cv e)))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))))
      (synWex c (synWex x (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
              (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))))
      p0029 p0032
  have p0034 := @gSnex (.cv c)
  have p0035 := @gOpkeq1 (.cv x) (synCsn (.cv c)) (synCopk C D)
  have p0036 :=
    @gEleq1d (.classEq (.cv x) (synCsn (.cv c))) (synCopk (.cv x) (synCopk C D))
      (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B) p0035
  have p0037 :=
    @gAnbi2d (.classEq (.cv x) (synCsn (.cv c)))
      (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))
      (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B))
      (synWbr (.cv c) (synCdif R (synCid)) (.cv e)) p0036
  have p0038 :=
    @gCeqsexv
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B)))
      x (synCsn (.cv c)) dv_cache_0023 dv_cache_0024 p0034 p0037
  have p0039 :=
    @gExbii
      (synWex x (synWa (.classEq (.cv x) (synCsn (.cv c)))
          (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B)))))
      (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
        (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B)))
      c p0038
  have p0040 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWex c (synWex x (synWa (.classEq (.cv x) (synCsn (.cv c)))
            (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
              (.classMem (synCopk (.cv x) (synCopk C D)) (synCfdsep A B))))))
      (synWex c (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B))))
      p0033 p0039
  have p0041 :=
    (Nominal.biimpRefl (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (.cv c) (synCsep2 C D)))))
  have p0042 :=
    @gN3bitr4g (synWa (.classMem C B) (.classMem D B))
      (synWex c (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (synCopk (synCsn (.cv c)) (synCopk C D)) (synCfdsep A B))))
      (synWex c (synWa (.classMem (.cv c) A)
          (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (.cv c) (synCsep2 C D))))
      p0005 p0040 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_kqrelex`. -/
@[expose]
noncomputable def gKqrelex (A : Class)
    (hyp_kqrelex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCkqrel A) (synCvv)) :=
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
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfKqrel x y A
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gSetconslem4 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gEqtr4i (synCkqrel A) (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A))
      (synCuni1 (synCuni1 (synCimak
            (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                      (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) A)))
      p0000 p0001
  have p0003 := @gVvex
  have p0005 := @gXpkex (synCvv) (synCvv) p0003 p0003
  have p0007 := @gXpkex (synCxpk (synCvv) (synCvv)) (synCvv) p0005 p0003
  have p0008 := @gSetconslem5
  have p0009 :=
    @gCnvkex
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
      p0008
  have p0010 :=
    @gInex (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv))
      (synCcnvk (synCcompl (synCimak
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
      p0007 p0009
  have p0011 :=
    @gImakex
      (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk (synCcompl
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      A p0010 hyp_kqrelex_1
  have p0012 :=
    @gUni1ex
      (synCimak (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk
            (synCcompl (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                  (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) A)
      p0011
  have p0013 :=
    @gUni1ex
      (synCuni1 (synCimak (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv))
            (synCcnvk (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                      (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) A))
      p0012
  have p0014 :=
    @gEqeltri (synCkqrel A)
      (synCuni1 (synCuni1 (synCimak
            (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                      (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) A)))
      (synCvv) p0002 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_kqrelbr`. -/
@[expose]
noncomputable def gKqrelbr (A : Class) (B : Class) (C : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_B_C : Disjoint B.fv C.fv) (hyp_kqrelbr_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_kqrelbr_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop B C) (synCkqrel A)) (.classMem (synCopk B C) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
  have p0002 := @gOpkeq1 (.cv x) B (.cv y)
  have p0003 :=
    @gEleq1d (.classEq (.cv x) B) (synCopk (.cv x) (.cv y)) (synCopk B (.cv y)) A p0002
  have p0004 := @gOpkeq2 (.cv y) C B
  have p0005 := @gEleq1d (.classEq (.cv y) C) (synCopk B (.cv y)) (synCopk B C) A p0004
  have p0006 :=
    @gOpelopab (.classMem (synCopk (.cv x) (.cv y)) A)
      (.classMem (synCopk B (.cv y)) A) (.classMem (synCopk B C) A) x y B C
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0003 hyp_kqrelbr_1 hyp_kqrelbr_2 p0003 p0005
  have p0007 :=
    @gBitri (.classMem (synCop B C) (synCkqrel A))
      (.classMem (synCop B C) (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) A)))
      (.classMem (synCopk B C) A) p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_fdminvalpex`. -/
@[expose]
noncomputable def gFdminvalpex (A : Class) (B : Class) (C : Class) (R : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (_dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdminvalpex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdminvalpex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdminvalpex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdminvalp R A B C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdminvalp R A B C))
  have p0001 := @gFdminsepex A B R hyp_fdminvalpex_1 hyp_fdminvalpex_2 hyp_fdminvalpex_3
  have p0002 := @gCnvkex (synCfdminsep R A B) p0001
  have p0003 := @gSnex C
  have p0004 := @gImakex (synCcnvk (synCfdminsep R A B)) (synCsn C) p0002 p0003
  have p0005 := @gUni1ex (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)) p0004
  have p0006 :=
    @gEqeltri (synCfdminvalp R A B C)
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))) (synCvv)
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fdminvalpbr`. -/
@[expose]
noncomputable def gFdminvalpbr (z : Var) (A : Class) (B : Class) (C : Class) (R : Class)
    (_dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (_dv_A_R : Disjoint A.fv R.fv) (_dv_A_z : z ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (_dv_B_R : Disjoint B.fv R.fv) (_dv_B_z : z ∉ B.fv) (_dv_C_R : Disjoint C.fv R.fv)
    (_dv_C_z : z ∉ C.fv) (_dv_R_z : z ∉ R.fv)
    (hyp_fdminvalpbr_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCfdminvalp R A B C))
        (.classMem (synCopk (synCsn (.cv z)) C) (synCfdminsep R A B))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdminvalp R A B C))
  have p0001 :=
    @gEleq2i (synCfdminvalp R A B C)
      (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))) (.cv z) p0000
  have p0002 := @gVex z
  have p0003 :=
    @gEluni1 (.cv z) (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)) p0002
  have p0004 :=
    @gBitri (.classMem (.cv z) (synCfdminvalp R A B C))
      (.classMem (.cv z) (synCuni1 (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C))))
      (.classMem (synCsn (.cv z)) (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)))
      p0001 p0003
  have p0005 := @gSnex (.cv z)
  have p0006 :=
    @gElimaksn (synCcnvk (synCfdminsep R A B)) C (synCsn (.cv z)) hyp_fdminvalpbr_1
      p0005
  have p0007 :=
    @gBitri (.classMem (.cv z) (synCfdminvalp R A B C))
      (.classMem (synCsn (.cv z)) (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn C)))
      (.classMem (synCopk C (synCsn (.cv z))) (synCcnvk (synCfdminsep R A B))) p0004
      p0006
  have p0009 :=
    @gOpkelcnvk C (synCsn (.cv z)) (synCfdminsep R A B) hyp_fdminvalpbr_1 p0005
  have p0010 :=
    @gBitri (.classMem (.cv z) (synCfdminvalp R A B C))
      (.classMem (synCopk C (synCsn (.cv z))) (synCcnvk (synCfdminsep R A B)))
      (.classMem (synCopk (synCsn (.cv z)) C) (synCfdminsep R A B)) p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_fdminqex`. -/
@[expose]
noncomputable def gFdminqex (A : Class) (B : Class) (R : Class)
    (hyp_fdminqex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdminqex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdminqex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdminq R A B) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfdminq R A B))
  have p0001 := @gFdminsepex A B R hyp_fdminqex_1 hyp_fdminqex_2 hyp_fdminqex_3
  have p0002 := @gKqrelex (synCfdminsep R A B) p0001
  have p0003 :=
    @gEqeltri (synCfdminq R A B) (synCkqrel (synCfdminsep R A B)) (synCvv) p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fdpivmap2ex`. -/
@[expose]
noncomputable def gFdpivmap2ex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdpivmap2 R A B) (synCvv)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p_ne_z : p ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_p : z ≠ p := Ne.symm fresh_p_ne_z
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0006 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint ((synCfdminsep R A B)).fv ((synCsn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((synCfdminsep R A B)).fv ((synCsn (.cv z))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (((Class.cv z)).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(Finset.disjoint_union_left.mpr
                    ⟨(show Disjoint ((A).fv) (((Class.cv z)).fv) from
                        (by
                          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                          exact
                            (show Disjoint ((A).fv) (({ z } : Finset Var)) from
                              (Finset.disjoint_singleton_right.mpr
                                (show z ∉ (A).fv from (by exact fresh_z_not_A)))))),
                      (show Disjoint ((B).fv) (((Class.cv z)).fv) from
                        (by
                          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                          exact
                            (show Disjoint ((B).fv) (({ z } : Finset Var)) from
                              (Finset.disjoint_singleton_right.mpr
                                (show z ∉ (B).fv from (by exact fresh_z_not_B))))))⟩),
                  (show Disjoint ((R).fv) (((Class.cv z)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((R).fv) (({ z } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show z ∉ (R).fv from (by exact fresh_z_not_R))))))⟩))))
  have dv_cache_0008 : Disjoint ((synCfdminsep R A B)).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((synCfdminsep R A B)).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({ p } : Finset Var)) from
              (Finset.disjoint_union_left.mpr
                ⟨(Finset.disjoint_union_left.mpr
                    ⟨(show Disjoint ((A).fv) (({ p } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show p ∉ (A).fv from (by exact fresh_p_not_A)))),
                      (show Disjoint ((B).fv) (({ p } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show p ∉ (B).fv from (by exact fresh_p_not_B))))⟩),
                  (show Disjoint ((R).fv) (({ p } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show p ∉ (R).fv from (by exact fresh_p_not_R))))⟩))))
  have dv_cache_0009 : Disjoint ((synCsn (.cv z))).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((synCsn (.cv z))).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((Class.cv z)).fv) (({ p } : Finset Var)) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ z } : Finset Var)) (({ p } : Finset Var)) from
                    (Finset.disjoint_singleton_left.mpr
                      (show z ∉ ({ p } : Finset Var) from
                        (by
                          simpa only [Finset.mem_singleton] using
                            (show z ≠ p from (by exact fresh_z_ne_p))))))))))
  have dv_cache_0010 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0011 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0012 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0013 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0014 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0015 : z ∉ ((Class.cv p)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0016 : z ∉ (R).fv :=
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
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_p_not_B, or_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((synCfdminq R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq,
          Finset.mem_union, fresh_p_not_A, fresh_p_not_B, fresh_p_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0019 : z ∉ ((synCfdminq R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0020 : z ∉ ((synCfdminvalp R A B (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_p, fresh_z_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0021 : p ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ z from (by exact fresh_p_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdpivmap2 A B R p
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := (Nominal.classEqRefl (synCfdminq R A B))
  have p0002 :=
    @gEleq2i (synCfdminq R A B) (synCkqrel (synCfdminsep R A B))
      (synCop (synCsn (.cv z)) (.cv p)) p0001
  have p0003 := @gSnex (.cv z)
  have p0004 := @gVex p
  have p0005 :=
    @gKqrelbr (synCfdminsep R A B) (synCsn (.cv z)) (.cv p) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0003 p0004
  have p0006 :=
    @gBitri (.classMem (synCop (synCsn (.cv z)) (.cv p)) (synCfdminq R A B))
      (.classMem (synCop (synCsn (.cv z)) (.cv p)) (synCkqrel (synCfdminsep R A B)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv p)) (synCfdminsep R A B)) p0002 p0005
  have p0008 :=
    @gFdminvalpbr z A B (.cv p) R dv_cache_0001 dv_cache_0010 dv_cache_0002 dv_cache_0011
      dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      p0004
  have p0009 :=
    @gBicomi (.classMem (.cv z) (synCfdminvalp R A B (.cv p)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv p)) (synCfdminsep R A B)) p0008
  have p0010 :=
    @gBitri (.classMem (synCop (synCsn (.cv z)) (.cv p)) (synCfdminq R A B))
      (.classMem (synCopk (synCsn (.cv z)) (.cv p)) (synCfdminsep R A B))
      (.classMem (.cv z) (synCfdminvalp R A B (.cv p))) p0006 p0009
  have p0011 :=
    @gReleqmpt p z (synCxpk B B) (synCfdminq R A B) (synCfdminvalp R A B (.cv p))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0010
  have p0012 :=
    @gEqtr4i (synCfdpivmap2 R A B)
      (synCmpt p (synCxpk B B) (synCfdminvalp R A B (.cv p)))
      (synCin (synCxp (synCxpk B B) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdminq R A B)))
              (synC1c)))))
      p0000 p0011
  have p0013 := @gXpkex B B hyp_fdpivmap2ex_3 hyp_fdpivmap2ex_3
  have p0014 := @gFdminqex A B R hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0015 := @gMptexlem (synCxpk B B) (synCfdminq R A B) p0013 p0014
  have p0016 :=
    @gEqeltri (synCfdpivmap2 R A B)
      (synCin (synCxp (synCxpk B B) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdminq R A B)))
              (synC1c)))))
      (synCvv) p0012 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_fdpivmap2fn`. -/
@[expose]
noncomputable def gFdpivmap2fn (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWfn (synCfdpivmap2 R A B) (synCxpk B B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0005 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0007 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_p_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @gFdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdpivmap2 A B R p
      dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @gFnmpti p (synCxpk B B) (synCfdminvalp R A B (.cv p)) (synCfdpivmap2 R A B)
      dv_cache_0010 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fdpivrange2ex`. -/
@[expose]
noncomputable def gFdpivrange2ex (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCfdpivrange2 R A B) (synCvv)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p_ne_z : p ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_p : z ≠ p := Ne.symm fresh_p_ne_z
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0004 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0005 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0006 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0007 : Disjoint ((synCfdminsep R A B)).fv ((synCsn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((synCfdminsep R A B)).fv ((synCsn (.cv z))).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
          exact
            (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (((Class.cv z)).fv) from
              (Finset.disjoint_union_left.mpr
                ⟨(Finset.disjoint_union_left.mpr
                    ⟨(show Disjoint ((A).fv) (((Class.cv z)).fv) from
                        (by
                          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                          exact
                            (show Disjoint ((A).fv) (({ z } : Finset Var)) from
                              (Finset.disjoint_singleton_right.mpr
                                (show z ∉ (A).fv from (by exact fresh_z_not_A)))))),
                      (show Disjoint ((B).fv) (((Class.cv z)).fv) from
                        (by
                          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                          exact
                            (show Disjoint ((B).fv) (({ z } : Finset Var)) from
                              (Finset.disjoint_singleton_right.mpr
                                (show z ∉ (B).fv from (by exact fresh_z_not_B))))))⟩),
                  (show Disjoint ((R).fv) (((Class.cv z)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((R).fv) (({ z } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show z ∉ (R).fv from (by exact fresh_z_not_R))))))⟩))))
  have dv_cache_0008 : Disjoint ((synCfdminsep R A B)).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint ((synCfdminsep R A B)).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminsep,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({ p } : Finset Var)) from
              (Finset.disjoint_union_left.mpr
                ⟨(Finset.disjoint_union_left.mpr
                    ⟨(show Disjoint ((A).fv) (({ p } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show p ∉ (A).fv from (by exact fresh_p_not_A)))),
                      (show Disjoint ((B).fv) (({ p } : Finset Var)) from
                        (Finset.disjoint_singleton_right.mpr
                          (show p ∉ (B).fv from (by exact fresh_p_not_B))))⟩),
                  (show Disjoint ((R).fv) (({ p } : Finset Var)) from
                    (Finset.disjoint_singleton_right.mpr
                      (show p ∉ (R).fv from (by exact fresh_p_not_R))))⟩))))
  have dv_cache_0009 : Disjoint ((synCsn (.cv z))).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (show Disjoint ((synCsn (.cv z))).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (((Class.cv z)).fv) (({ p } : Finset Var)) from
              (by
                rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                exact
                  (show Disjoint (({ z } : Finset Var)) (({ p } : Finset Var)) from
                    (Finset.disjoint_singleton_left.mpr
                      (show z ∉ ({ p } : Finset Var) from
                        (by
                          simpa only [Finset.mem_singleton] using
                            (show z ≠ p from (by exact fresh_z_ne_p))))))))))
  have dv_cache_0010 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0011 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0012 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0013 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0014 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0015 : z ∉ ((Class.cv p)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0016 : z ∉ (R).fv :=
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
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_p_not_B, or_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((synCfdminq R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq,
          Finset.mem_union, fresh_p_not_A, fresh_p_not_B, fresh_p_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0019 : z ∉ ((synCfdminq R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminq,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0020 : z ∉ ((synCfdminvalp R A B (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_p, fresh_z_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0021 : p ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ z from (by exact fresh_p_ne_z))
  have p0000 := (Nominal.classEqRefl (synCfdpivrange2 R A B))
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdpivmap2 A B R p
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0002 := (Nominal.classEqRefl (synCfdminq R A B))
  have p0003 :=
    @gEleq2i (synCfdminq R A B) (synCkqrel (synCfdminsep R A B))
      (synCop (synCsn (.cv z)) (.cv p)) p0002
  have p0004 := @gSnex (.cv z)
  have p0005 := @gVex p
  have p0006 :=
    @gKqrelbr (synCfdminsep R A B) (synCsn (.cv z)) (.cv p) dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0004 p0005
  have p0007 :=
    @gBitri (.classMem (synCop (synCsn (.cv z)) (.cv p)) (synCfdminq R A B))
      (.classMem (synCop (synCsn (.cv z)) (.cv p)) (synCkqrel (synCfdminsep R A B)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv p)) (synCfdminsep R A B)) p0003 p0006
  have p0009 :=
    @gFdminvalpbr z A B (.cv p) R dv_cache_0001 dv_cache_0010 dv_cache_0002 dv_cache_0011
      dv_cache_0012 dv_cache_0004 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      p0005
  have p0010 :=
    @gBicomi (.classMem (.cv z) (synCfdminvalp R A B (.cv p)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv p)) (synCfdminsep R A B)) p0009
  have p0011 :=
    @gBitri (.classMem (synCop (synCsn (.cv z)) (.cv p)) (synCfdminq R A B))
      (.classMem (synCopk (synCsn (.cv z)) (.cv p)) (synCfdminsep R A B))
      (.classMem (.cv z) (synCfdminvalp R A B (.cv p))) p0007 p0010
  have p0012 :=
    @gReleqmpt p z (synCxpk B B) (synCfdminq R A B) (synCfdminvalp R A B (.cv p))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 p0011
  have p0013 :=
    @gEqtr4i (synCfdpivmap2 R A B)
      (synCmpt p (synCxpk B B) (synCfdminvalp R A B (.cv p)))
      (synCin (synCxp (synCxpk B B) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdminq R A B)))
              (synC1c)))))
      p0001 p0012
  have p0014 := @gXpkex B B hyp_fdpivmap2ex_3 hyp_fdpivmap2ex_3
  have p0015 := @gFdminqex A B R hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0016 := @gMptexlem (synCxpk B B) (synCfdminq R A B) p0014 p0015
  have p0017 :=
    @gEqeltri (synCfdpivmap2 R A B)
      (synCin (synCxp (synCxpk B B) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCfdminq R A B)))
              (synC1c)))))
      (synCvv) p0013 p0016
  have p0018 := @gRnex (synCfdpivmap2 R A B) p0017
  have p0019 :=
    @gEqeltri (synCfdpivrange2 R A B) (synCrn (synCfdpivmap2 R A B)) (synCvv) p0000
      p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_fdpivmap2onto`. -/
@[expose]
noncomputable def gFdpivmap2onto (A : Class) (B : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv)
    (dv_B_R : Disjoint B.fv R.fv)
    (hyp_fdpivmap2ex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivmap2ex_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivmap2ex_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCfdpivrange2 R A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact fresh_p_not_A))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact fresh_p_not_B))))))
  have dv_cache_0005 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact fresh_p_not_R))))))
  have dv_cache_0007 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_R, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, fresh_p_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @gFdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdpivmap2ex_1 hyp_fdpivmap2ex_2 hyp_fdpivmap2ex_3
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdpivmap2 A B R p
      dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @gFnmpti p (synCxpk B B) (synCfdminvalp R A B (.cv p)) (synCfdpivmap2 R A B)
      dv_cache_0010 p0000 p0001
  have p0003 := @gDffn4 (synCxpk B B) (synCfdpivmap2 R A B)
  have p0004 :=
    @gMpbi (synWfn (synCfdpivmap2 R A B) (synCxpk B B))
      (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCrn (synCfdpivmap2 R A B)))
      p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCfdpivrange2 R A B))
  have p0006 := @gEqcomi (synCfdpivrange2 R A B) (synCrn (synCfdpivmap2 R A B)) p0005
  have p0007 :=
    @gFoeq3 (synCrn (synCfdpivmap2 R A B)) (synCfdpivrange2 R A B) (synCxpk B B)
      (synCfdpivmap2 R A B)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gMpbi
      (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCrn (synCfdpivmap2 R A B)))
      (synWfo (synCfdpivmap2 R A B) (synCxpk B B) (synCfdpivrange2 R A B)) p0004 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fdpivmap2val`. -/
@[expose]
noncomputable def gFdpivmap2val (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv)
    (hyp_fdpivmap2val_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivmap2val_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivmap2val_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv p) (synCxpk B B))
        (.classEq (synCfv (synCfdpivmap2 R A B) (.cv p)) (synCfdminvalp R A B (.cv p)))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (A).fv from (by exact dv_A_p))))))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (B).fv ((Class.cv p)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((B).fv) (({ p } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show p ∉ (B).fv from (by exact dv_B_p))))))
  have dv_cache_0005 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint ((Class.cv p)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv p)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ p } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show p ∉ (R).fv from (by exact dv_R_p))))))
  have dv_cache_0007 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_p, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_p, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_p, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, dv_B_p, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem (.cv p) (synCxpk B B))
  have p0001 :=
    @gFdminvalpex A B (.cv p) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fdpivmap2val_1 hyp_fdpivmap2val_2 hyp_fdpivmap2val_3
  have p0002 :=
    @gA1i (.classMem (synCfdminvalp R A B (.cv p)) (synCvv))
      (.classMem (.cv p) (synCxpk B B)) p0001
  have p0003 :=
    @gJca (.classMem (.cv p) (synCxpk B B)) (.classMem (.cv p) (synCxpk B B))
      (.classMem (synCfdminvalp R A B (.cv p)) (synCvv)) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFdpivmap2 A B R p
      dv_cache_0001 dv_cache_0003 dv_cache_0007 dv_cache_0005 dv_cache_0008 dv_cache_0009
  have p0005 :=
    @gFvmpt2 p (synCxpk B B) (synCfdminvalp R A B (.cv p)) (synCvv)
      (synCfdpivmap2 R A B) dv_cache_0010 p0004
  have p0006 :=
    @gSyl (.classMem (.cv p) (synCxpk B B))
      (synWa (.classMem (.cv p) (synCxpk B B))
        (.classMem (synCfdminvalp R A B (.cv p)) (synCvv)))
      (.classEq (synCfv (synCfdpivmap2 R A B) (.cv p)) (synCfdminvalp R A B (.cv p)))
      p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fdpivrange2br`. -/
@[expose]
noncomputable def gFdpivrange2br (A : Class) (B : Class) (C : Class) (R : Class)
    (p : Var) (dv_A_B : Disjoint A.fv B.fv) (_dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_p : p ∉ A.fv) (_dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_p : p ∉ B.fv) (_dv_C_R : Disjoint C.fv R.fv)
    (dv_C_p : p ∉ C.fv) (dv_R_p : p ∉ R.fv)
    (hyp_fdpivrange2br_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_fdpivrange2br_2 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fdpivrange2br_3 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem C (synCfdpivrange2 R A B))
        (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) C))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : p ∉ ((synCxpk B B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          Finset.mem_union, dv_B_p, or_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((synCfdpivmap2 R A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2,
          Finset.mem_union, dv_A_p, dv_B_p, dv_R_p, or_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_p, not_false_eq_true])
  have dv_cache_0008 : p ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_p, not_false_eq_true])
  have dv_cache_0009 : p ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_p, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCfdpivrange2 R A B))
  have p0001 :=
    @gEleq2i (synCfdpivrange2 R A B) (synCrn (synCfdpivmap2 R A B)) C p0000
  have p0002 :=
    @gFdpivmap2fn A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdpivrange2br_1
      hyp_fdpivrange2br_2 hyp_fdpivrange2br_3
  have p0003 :=
    @gFvelrnb p (synCxpk B B) C (synCfdpivmap2 R A B) dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gFdpivmap2val A B R p dv_cache_0001 dv_cache_0002 dv_cache_0007 dv_cache_0003
      dv_cache_0008 dv_cache_0009 hyp_fdpivrange2br_1 hyp_fdpivrange2br_2
      hyp_fdpivrange2br_3
  have p0006 :=
    @gEqeq1d (.classMem (.cv p) (synCxpk B B)) (synCfv (synCfdpivmap2 R A B) (.cv p))
      (synCfdminvalp R A B (.cv p)) C p0005
  have p0007 :=
    @gRexbiia (.classEq (synCfv (synCfdpivmap2 R A B) (.cv p)) C)
      (.classEq (synCfdminvalp R A B (.cv p)) C) p (synCxpk B B) p0006
  have p0008 :=
    @gBitri (.classMem C (synCrn (synCfdpivmap2 R A B)))
      (synWrex p (synCxpk B B) (.classEq (synCfv (synCfdpivmap2 R A B) (.cv p)) C))
      (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) C)) p0004 p0007
  have p0009 :=
    @gBitri (.classMem C (synCfdpivrange2 R A B))
      (.classMem C (synCrn (synCfdpivmap2 R A B)))
      (synWrex p (synCxpk B B) (.classEq (synCfdminvalp R A B (.cv p)) C)) p0001 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_fdminvalpss`. -/
@[expose]
noncomputable def gFdminvalpss (A : Class) (B : Class) (C : Class) (R : Class)
    (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_B_C : Disjoint B.fv C.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_C_R : Disjoint C.fv R.fv)
    (hyp_fdminvalpss_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf (synWss (synCfdminvalp R A B C) A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
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
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0009 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0010 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((synCfdminvalp R A B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdminvalp,
          Finset.mem_union, fresh_z_not_A, fresh_z_not_B, fresh_z_not_C, fresh_z_not_R,
          or_false, not_false_eq_true])
  have p0000 :=
    @gFdminvalpbr z A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      hyp_fdminvalpss_1
  have p0001 :=
    @gBiimpi (.classMem (.cv z) (synCfdminvalp R A B C))
      (.classMem (synCopk (synCsn (.cv z)) C) (synCfdminsep R A B)) p0000
  have p0002 := (Nominal.classEqRefl (synCfdminsep R A B))
  have p0003 := @gDifss (synCfdsep A B) (synCfdnonmin R A B)
  have p0004 :=
    @gEqsstri (synCfdminsep R A B) (synCdif (synCfdsep A B) (synCfdnonmin R A B))
      (synCfdsep A B) p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCfdsep A B))
  have p0006 := (Nominal.classEqRefl (synCsymdif (synCfde0 A B) (synCfde1 A B)))
  have p0007 :=
    @gEqtri (synCfdsep A B) (synCsymdif (synCfde0 A B) (synCfde1 A B))
      (synCun (synCdif (synCfde0 A B) (synCfde1 A B))
        (synCdif (synCfde1 A B) (synCfde0 A B)))
      p0005 p0006
  have p0008 := @gDifss (synCfde0 A B) (synCfde1 A B)
  have p0009 := (Nominal.classEqRefl (synCfde0 A B))
  have p0010 := @gInss2 (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B)
  have p0011 :=
    @gEqsstri (synCfde0 A B)
      (synCin (synCcomk (synCfdprj0) (synCfdmem)) (synCfddom A B)) (synCfddom A B)
      p0009 p0010
  have p0012 :=
    @gSstri (synCdif (synCfde0 A B) (synCfde1 A B)) (synCfde0 A B) (synCfddom A B)
      p0008 p0011
  have p0013 := @gDifss (synCfde1 A B) (synCfde0 A B)
  have p0014 := (Nominal.classEqRefl (synCfde1 A B))
  have p0015 := @gInss2 (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B)
  have p0016 :=
    @gEqsstri (synCfde1 A B)
      (synCin (synCcomk (synCfdprj1) (synCfdmem)) (synCfddom A B)) (synCfddom A B)
      p0014 p0015
  have p0017 :=
    @gSstri (synCdif (synCfde1 A B) (synCfde0 A B)) (synCfde1 A B) (synCfddom A B)
      p0013 p0016
  have p0018 :=
    @gUnssi (synCdif (synCfde0 A B) (synCfde1 A B))
      (synCdif (synCfde1 A B) (synCfde0 A B)) (synCfddom A B) p0012 p0017
  have p0019 :=
    @gEqsstri (synCfdsep A B)
      (synCun (synCdif (synCfde0 A B) (synCfde1 A B))
        (synCdif (synCfde1 A B) (synCfde0 A B)))
      (synCfddom A B) p0007 p0018
  have p0020 :=
    @gSstri (synCfdminsep R A B) (synCfdsep A B) (synCfddom A B) p0004 p0019
  have p0021 :=
    @gSseli (synCfdminsep R A B) (synCfddom A B) (synCopk (synCsn (.cv z)) C) p0020
  have p0022 :=
    @gSyl (.classMem (.cv z) (synCfdminvalp R A B C))
      (.classMem (synCopk (synCsn (.cv z)) C) (synCfdminsep R A B))
      (.classMem (synCopk (synCsn (.cv z)) C) (synCfddom A B)) p0001 p0021
  have p0023 := (Nominal.classEqRefl (synCfddom A B))
  have p0024 :=
    @gEleq2i (synCfddom A B) (synCxpk (synCpw1 A) (synCxpk B B))
      (synCopk (synCsn (.cv z)) C) p0023
  have p0025 := @gSnex (.cv z)
  have p0026 :=
    @gOpkelxpk (synCsn (.cv z)) C (synCpw1 A) (synCxpk B B) p0025 hyp_fdminvalpss_1
  have p0027 :=
    @gBitri (.classMem (synCopk (synCsn (.cv z)) C) (synCfddom A B))
      (.classMem (synCopk (synCsn (.cv z)) C) (synCxpk (synCpw1 A) (synCxpk B B)))
      (synWa (.classMem (synCsn (.cv z)) (synCpw1 A)) (.classMem C (synCxpk B B)))
      p0024 p0026
  have p0028 :=
    @gSimplbi (.classMem (synCopk (synCsn (.cv z)) C) (synCfddom A B))
      (.classMem (synCsn (.cv z)) (synCpw1 A)) (.classMem C (synCxpk B B)) p0027
  have p0029 := @gSnelpw1 (.cv z) A
  have p0030 :=
    @gBiimpi (.classMem (synCsn (.cv z)) (synCpw1 A)) (.classMem (.cv z) A) p0029
  have p0031 :=
    @gN3syl (.classMem (.cv z) (synCfdminvalp R A B C))
      (.classMem (synCopk (synCsn (.cv z)) C) (synCfddom A B))
      (.classMem (synCsn (.cv z)) (synCpw1 A)) (.classMem (.cv z) A) p0022 p0028 p0030
  have p0032 := @gSsriv z (synCfdminvalp R A B C) A dv_cache_0011 dv_cache_0004 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_elfpiv`. -/
@[expose]
noncomputable def gElfpiv (A : Class) (B : Class) (C : Class) (R : Class) (e : Var)
    (c : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (_dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv)
    (_dv_B_e : e ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv)
    (_dv_C_e : e ∉ C.fv) (dv_R_c : c ∉ R.fv) (_dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (synWb (.classMem (.cv e) (synCfpiv R A B C))
        (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 B C))) (synWral c A
            (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c)))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ ({ e } : Finset Var) ∪ ({ c } : Finset Var)
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_e : b ≠ e := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_c : b ≠ c := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have dv_cache_0001 : c ∉ ((Wff.classEq (.cv b) (.cv e))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_b, dv_c_e, or_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint (A).fv (B).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0003 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0006 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_c, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0008 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0009 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0010 : c ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_c, not_false_eq_true])
  have dv_cache_0011 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0012 : b ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_C, not_false_eq_true])
  have dv_cache_0013 : c ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_c, not_false_eq_true])
  have dv_cache_0014 : b ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0015 : c ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_c, not_false_eq_true])
  have dv_cache_0016 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0017 : b ∉ ((Class.cv e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_e, not_false_eq_true])
  have dv_cache_0018 :
    b ∉
      ((synWa (.classMem (.cv e) (synCsep2 B C)) (synWral c A
            (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_csep2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_e, fresh_b_not_B,
          fresh_b_not_C, fresh_b_not_A, fresh_b_ne_c, fresh_b_not_R, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gId (.classEq (.cv b) (.cv e))
  have p0001 := @gEleq1d (.classEq (.cv b) (.cv e)) (.cv b) (.cv e) (synCsep2 B C) p0000
  have p0003 := @gBreq1d (.classEq (.cv b) (.cv e)) (.cv b) (.cv e) (.cv c) R p0000
  have p0004 :=
    @gImbi2d (.classEq (.cv b) (.cv e)) (synWbr (.cv b) R (.cv c))
      (synWbr (.cv e) R (.cv c)) (.classMem (.cv c) (synCsep2 B C)) p0003
  have p0005 :=
    @gRalbidv (.classEq (.cv b) (.cv e))
      (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv b) R (.cv c)))
      (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c))) c A
      dv_cache_0001 p0004
  have p0006 :=
    @gAnbi12d (.classEq (.cv b) (.cv e)) (.classMem (.cv b) (synCsep2 B C))
      (.classMem (.cv e) (synCsep2 B C))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv b) R (.cv c))))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c))))
      p0001 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFpiv A B C R b c
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0008 :=
    @gElrab2
      (synWa (.classMem (.cv b) (synCsep2 B C)) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv b) R (.cv c)))))
      (synWa (.classMem (.cv e) (synCsep2 B C)) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c)))))
      b (.cv e) A (synCfpiv R A B C) dv_cache_0017 dv_cache_0005 dv_cache_0018 p0006
      p0007
  have p0009 :=
    @gAnass (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 B C))
      (synWral c A (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c))))
  have p0010 :=
    @gBitr4i (.classMem (.cv e) (synCfpiv R A B C))
      (synWa (.classMem (.cv e) A) (synWa (.classMem (.cv e) (synCsep2 B C)) (synWral c A
            (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c))))))
      (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 B C))) (synWral c A
          (.imp (.classMem (.cv c) (synCsep2 B C)) (synWbr (.cv e) R (.cv c)))))
      p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_fdminsepval0J`. -/
@[expose]
noncomputable def gFdminsepval0J (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (e : Var) (c : Var) (dv_A_B : Disjoint A.fv B.fv)
    (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv)
    (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv)
    (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv)
    (dv_B_R : Disjoint B.fv R.fv) (dv_B_c : c ∉ B.fv) (dv_B_e : e ∉ B.fv)
    (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_c : c ∉ C.fv)
    (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv) (dv_D_c : c ∉ D.fv)
    (dv_D_e : e ∉ D.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf
      (.imp (synWa (.classMem C B) (.classMem D B)) (synWb
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
          (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (.neg
              (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
                  (.classMem (.cv c) (synCsep2 C D)))))))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact
      (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : e ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_e, not_false_eq_true])
  have dv_cache_0005 : Disjoint (B).fv (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0006 : Disjoint (B).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0007 : e ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_e, not_false_eq_true])
  have dv_cache_0008 : Disjoint (C).fv (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0009 : e ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_e, not_false_eq_true])
  have dv_cache_0010 : e ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_e, not_false_eq_true])
  have dv_cache_0011 : Disjoint (A).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0012 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_c, not_false_eq_true])
  have dv_cache_0013 : Disjoint (B).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0014 : c ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_c, not_false_eq_true])
  have dv_cache_0015 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0016 : c ∉ (C).fv :=
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
        simp only [dv_C_c, not_false_eq_true])
  have dv_cache_0017 : Disjoint (D).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0018 : c ∉ (D).fv :=
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
        simp only [dv_D_c, not_false_eq_true])
  have dv_cache_0019 : c ∉ (R).fv :=
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
        simp only [dv_R_c, not_false_eq_true])
  have dv_cache_0020 : e ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_e, not_false_eq_true])
  have dv_cache_0021 : c ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show c ≠ e from (by exact dv_c_e))
  have p0000 := (Nominal.classEqRefl (synCfdminsep R A B))
  have p0001 :=
    @gEleq2i (synCfdminsep R A B) (synCdif (synCfdsep A B) (synCfdnonmin R A B))
      (synCopk (synCsn (.cv e)) (synCopk C D)) p0000
  have p0002 :=
    @gEldif (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B)
      (synCfdnonmin R A B)
  have p0003 :=
    @gBitri (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D))
        (synCdif (synCfdsep A B) (synCfdnonmin R A B)))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B)) (.neg
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))))
      p0001 p0002
  have p0004 :=
    @gA1i
      (synWb (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
        (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B)) (.neg
            (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B)))))
      (synWa (.classMem C B) (.classMem D B)) p0003
  have p0005 :=
    @gFdsepvalJ A B C D e dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0006 :=
    @gFdnonminval0J A B C D R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0011
      dv_cache_0012 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0013 dv_cache_0014
      dv_cache_0007 dv_cache_0008 dv_cache_0015 dv_cache_0016 dv_cache_0009 dv_cache_0017
      dv_cache_0018 dv_cache_0010 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0007 :=
    @gNotbid (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))
      (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
          (.classMem (.cv c) (synCsep2 C D))))
      p0006
  have p0008 :=
    @gAnbi12d (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B))
      (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D)))
      (.neg (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B)))
      (.neg (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
            (.classMem (.cv c) (synCsep2 C D)))))
      p0005 p0007
  have p0009 :=
    @gBitrd (synWa (.classMem C B) (.classMem D B))
      (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdminsep R A B))
      (synWa (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdsep A B)) (.neg
          (.classMem (synCopk (synCsn (.cv e)) (synCopk C D)) (synCfdnonmin R A B))))
      (synWa (synWa (.classMem (.cv e) A) (.classMem (.cv e) (synCsep2 C D))) (.neg
          (synWrex c A (synWa (synWbr (.cv c) (synCdif R (synCid)) (.cv e))
              (.classMem (.cv c) (synCsep2 C D))))))
      p0004 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wppwepo`. -/
@[expose]
noncomputable def gWppwepo (A : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr R (synCwe) A) (synWbr R (synCpartial) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwe))
  have p0001 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0000
  have p0002 := @gBrin R A (synCstrict) (synCfound)
  have p0003 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0001 p0002
  have p0004 :=
    @gSimplbi (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCfound) A) p0003
  have p0005 := @gSopc A R
  have p0006 :=
    @gSimplbi (synWbr R (synCstrict) A) (synWbr R (synCpartial) A)
      (synWbr R (synCconnex) A) p0005
  have p0007 :=
    @gSyl (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCpartial) A) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppweref`. -/
@[expose]
noncomputable def gWppweref (A : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr R (synCwe) A) (synWbr R (synCref) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwe))
  have p0001 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0000
  have p0002 := @gBrin R A (synCstrict) (synCfound)
  have p0003 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0001 p0002
  have p0004 :=
    @gSimplbi (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCfound) A) p0003
  have p0005 := @gSopc A R
  have p0006 :=
    @gSimplbi (synWbr R (synCstrict) A) (synWbr R (synCpartial) A)
      (synWbr R (synCconnex) A) p0005
  have p0007 :=
    @gSyl (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCpartial) A) p0004 p0006
  have p0008 := @gPorta A R
  have p0009 :=
    @gSimp1bi (synWbr R (synCpartial) A) (synWbr R (synCref) A)
      (synWbr R (synCtrans) A) (synWbr R (synCantisym) A) p0008
  have p0010 :=
    @gSyl (synWbr R (synCwe) A) (synWbr R (synCpartial) A) (synWbr R (synCref) A)
      p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_wppweconnex`. -/
@[expose]
noncomputable def gWppweconnex (A : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr R (synCwe) A) (synWbr R (synCconnex) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwe))
  have p0001 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0000
  have p0002 := @gBrin R A (synCstrict) (synCfound)
  have p0003 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0001 p0002
  have p0004 :=
    @gSimplbi (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCfound) A) p0003
  have p0005 := @gSopc A R
  have p0006 :=
    @gSimprbi (synWbr R (synCstrict) A) (synWbr R (synCpartial) A)
      (synWbr R (synCconnex) A) p0005
  have p0007 :=
    @gSyl (synWbr R (synCwe) A) (synWbr R (synCstrict) A) (synWbr R (synCconnex) A)
      p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppweantisym`. -/
@[expose]
noncomputable def gWppweantisym (A : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr R (synCwe) A) (synWbr R (synCantisym) A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwe))
  have p0001 := @gBreqi R A (synCwe) (synCin (synCstrict) (synCfound)) p0000
  have p0002 := @gBrin R A (synCstrict) (synCfound)
  have p0003 :=
    @gBitri (synWbr R (synCwe) A) (synWbr R (synCin (synCstrict) (synCfound)) A)
      (synWa (synWbr R (synCstrict) A) (synWbr R (synCfound) A)) p0001 p0002
  have p0004 :=
    @gSimplbi (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCfound) A) p0003
  have p0005 := @gSopc A R
  have p0006 :=
    @gSimplbi (synWbr R (synCstrict) A) (synWbr R (synCpartial) A)
      (synWbr R (synCconnex) A) p0005
  have p0007 :=
    @gSyl (synWbr R (synCwe) A) (synWbr R (synCstrict) A)
      (synWbr R (synCpartial) A) p0004 p0006
  have p0008 := @gPorta A R
  have p0009 :=
    @gSimp3bi (synWbr R (synCpartial) A) (synWbr R (synCref) A)
      (synWbr R (synCtrans) A) (synWbr R (synCantisym) A) p0008
  have p0010 :=
    @gSyl (synWbr R (synCwe) A) (synWbr R (synCpartial) A)
      (synWbr R (synCantisym) A) p0007 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end
